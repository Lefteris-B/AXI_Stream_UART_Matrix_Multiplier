module skid_buffer_tb;
    // Parameters
    localparam WIDTH = 8;
    localparam CLK_PERIOD = 10;
    
    // Signals
    logic              clk;
    logic              rst_n;
    logic              s_valid;
    logic              s_ready;
    logic [WIDTH-1:0]  s_data;
    logic              m_valid;
    logic              m_ready;
    logic [WIDTH-1:0]  m_data;
    
    // Test signals
    logic [WIDTH-1:0]  test_data[$];
    logic [WIDTH-1:0]  received_data[$];
    int                transaction_count;
    
    // DUT
    skid_buffer #(
        .WIDTH(WIDTH)
    ) dut (.*);
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Waveform dump
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    // Reset task
    task automatic reset;
        rst_n = 0;
        s_valid = 0;
        m_ready = 0;
        s_data = '0;
        test_data.delete();
        received_data.delete();
        transaction_count = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);
    endtask

    // Sender task
    task automatic send_data(input logic [WIDTH-1:0] data);
        s_data = data;
        s_valid = 1;
        test_data.push_back(data);
        do begin
            @(posedge clk);
        end while (!s_ready);
        @(posedge clk);
        s_valid = 0;
        s_data = 'x;
    endtask

    // Receiver task
    task automatic receive_data;
        m_ready = 1;
        do begin
            @(posedge clk);
        end while (!m_valid);
        received_data.push_back(m_data);
        transaction_count++;
        @(posedge clk);
        m_ready = 0;
    endtask

    // Test stimulus
    initial begin
        reset();
        
        // Test 1: Single transfer
        fork
            send_data(8'hA5);
            receive_data();
        join
        
        repeat(2) @(posedge clk);
        
        // Test 2: Back-to-back transfers with gaps
        fork
            begin
                repeat(3) begin
                    automatic logic [WIDTH-1:0] data = $random;
                    send_data(data);
                    @(posedge clk);
                end
            end
            begin
                repeat(3) begin
                    receive_data();
                    @(posedge clk);
                end
            end
        join
        
        repeat(2) @(posedge clk);
        
        // Test 3: Backpressure test
        fork
            begin
                send_data(8'h55);
                send_data(8'hAA);
            end
            begin
                m_ready = 0;
                repeat(3) @(posedge clk);
                receive_data();
                receive_data();
            end
        join
        
        // Verify results
        repeat(5) @(posedge clk);
        
        if (test_data.size() != received_data.size()) begin
            $error("Size mismatch! Sent: %0d, Received: %0d",
                   test_data.size(), received_data.size());
        end else begin
            automatic int errors = 0;
            while (test_data.size() > 0) begin
                automatic logic [WIDTH-1:0] exp = test_data.pop_front();
                automatic logic [WIDTH-1:0] got = received_data.pop_front();
                if (exp !== got) begin
                    $error("Data mismatch! Expected: %h, Got: %h", exp, got);
                    errors++;
                end
            end
            if (errors == 0)
                $display("Test passed! All data matched correctly.");
        end
        
        $finish;
    end

    // Protocol assertions
    property p_valid_stable;
        @(posedge clk) disable iff (!rst_n)
        m_valid && !m_ready |=> $stable(m_valid);
    endproperty
    
    property p_data_stable;
        @(posedge clk) disable iff (!rst_n)
        m_valid |=> $stable(m_data);
    endproperty
    
    property p_valid_ready;
        @(posedge clk) disable iff (!rst_n)
        s_valid && s_ready |-> ##[1:2] m_valid;
    endproperty
    
    property p_valid_transfer;
        @(posedge clk) disable iff (!rst_n)
        m_valid && m_ready |-> !$stable(m_data);
    endproperty

    assert property(p_valid_stable)
        else $error("Valid dropped during backpressure");
        
    assert property(p_data_stable)
        else $error("Data changed when valid was high");
        
    assert property(p_valid_ready)
        else $error("Valid not properly propagated");

    // Monitor
    always @(posedge clk) begin
        if (m_valid && m_ready)
            $display("Time=%0t: Transferred data = 0x%h", $time, m_data);
    end

    // Coverage
    covergroup skid_buffer_cov @(posedge clk);
        option.per_instance = 1;
        
        cp_handshake: coverpoint {s_valid, s_ready, m_valid, m_ready} {
            bins normal_transfer   = {4'b1111};
            bins input_wait       = {4'b1011};
            bins output_wait      = {4'b1110};
            bins skid_active      = {4'b1010};
            bins idle            = {4'b0000};
        }
    endgroup

    skid_buffer_cov cov = new();

    // Timeout watchdog
    initial begin
        #2000 $error("Simulation timeout!");
        $finish;
    end

endmodule