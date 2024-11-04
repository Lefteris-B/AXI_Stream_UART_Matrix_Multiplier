`timescale 1ns/1ps

module uart_rx_tb;
    // Testbench parameters
    localparam CLOCK_FREQ = 200_000_000;
    localparam BAUD_RATE = 9600;
    localparam BITS_PER_WORD = 8;
    localparam NUM_WORDS = 3;
    localparam CLOCKS_PER_PULSE = CLOCK_FREQ/BAUD_RATE;
    localparam W_OUT = NUM_WORDS * BITS_PER_WORD;
    
    // DUT signals
    logic clk;
    logic rst_n;
    logic rx;
    logic m_valid;
    logic [W_OUT-1:0] m_data;
    
    // Testbench signals
    logic [W_OUT-1:0] expected_data;
    int reception_count;
    logic sending_data;
    
    // Instantiate DUT
    uart_rx #(
        .CLOCK_FREQ(CLOCK_FREQ),
        .BAUD_RATE(BAUD_RATE),
        .BITS_PER_WORD(BITS_PER_WORD),
        .NUM_WORDS(NUM_WORDS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .m_valid(m_valid),
        .m_data(m_data)
    );
    
    // Clock generation
    initial begin
      $dumpfile("dump.vcd"); 
      $dumpvars;
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Reset generation
    initial begin
        rst_n = 0;
        #100 rst_n = 1;
    end
    
    // Counter for receptions
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reception_count <= 0;
        else if (m_valid)
            reception_count <= reception_count + 1;
    end

    // Task to send a UART packet
    task automatic send_uart_packet(input logic [W_OUT-1:0] data);
        sending_data = 1;
        expected_data = data;
        
        for (int word = 0; word < NUM_WORDS; word++) begin
            // Start bit
            rx = 0;
            repeat(CLOCKS_PER_PULSE) @(posedge clk);
            
            // Data bits
            for (int bit = 0; bit < BITS_PER_WORD; bit++) begin
                rx = data[word*BITS_PER_WORD + bit];
                repeat(CLOCKS_PER_PULSE) @(posedge clk);
            end
            
            // Stop bit
            rx = 1;
            repeat(CLOCKS_PER_PULSE) @(posedge clk);
        end
        
        sending_data = 0;
    endtask

    // Task to introduce glitches
    task automatic add_glitch(input int duration);
        logic old_value = rx;
        rx = ~rx;
        repeat(duration) @(posedge clk);
        rx = old_value;
    endtask

    // Properties and Assertions
    
    // Property 1: Reset behavior
    property p_reset_behavior;
        @(posedge clk)
        !rst_n |=> !m_valid && (m_data == '0);
    endproperty
    assert property(p_reset_behavior) else
        $error("Reset behavior verification failed");
    
    // Property 2: Valid signal duration
    property p_valid_duration;
        @(posedge clk) disable iff (!rst_n)
        m_valid |=> !m_valid;
    endproperty
    assert property(p_valid_duration) else
        $error("Valid signal duration violation");
    
    // Property 3: Idle state RX value
    property p_idle_rx;
        @(posedge clk) disable iff (!rst_n)
        (!sending_data) |-> rx == 1;
    endproperty
    assert property(p_idle_rx) else
        $error("Idle RX value violation");
    
    // Property 4: Start bit detection
    sequence start_bit_seq;
        !rx [*CLOCKS_PER_PULSE];
    endsequence
    
    property p_start_bit;
        @(posedge clk) disable iff (!rst_n)
        $fell(rx) |-> start_bit_seq;
    endproperty
    assert property(p_start_bit) else
        $error("Start bit sequence violation");
    
    // Property 5: Data verification
    property p_data_verify;
        @(posedge clk) disable iff (!rst_n)
        m_valid |-> (m_data == expected_data);
    endproperty
    assert property(p_data_verify) else
        $error("Data verification failed");

    // Coverage
    covergroup uart_rx_cov @(posedge clk);
        option.per_instance = 1;
        
        // Input coverage
        cp_rx: coverpoint rx {
            bins rx_values[] = {0,1};
            bins rx_transitions = (0=>1), (1=>0);
        }
        
        // Valid signal coverage
        cp_valid: coverpoint m_valid {
            bins valid_assert = {1};
            bins valid_deassert = {0};
        }
        
        // Data patterns coverage
        cp_data: coverpoint m_data[7:0] {
            bins zeros = {'h00};
            bins ones  = {'hFF};
            bins others = {['h01:'hFE]};
        }
        
        // Cross coverage
        rx_valid_cross: cross cp_rx, cp_valid;
    endgroup
    
    uart_rx_cov cg = new();
    
    // Stimulus and test scenarios
    initial begin
        // Initialize signals
        rx = 1;
        sending_data = 0;
        expected_data = 0;
        
        // Wait for reset
        @(posedge rst_n);
        repeat(10) @(posedge clk);
        
        // Test case 1: Simple pattern
        send_uart_packet({8'hA5, 8'h5A, 8'hF0});
        
        // Wait for reception
        wait(m_valid);
        repeat(10) @(posedge clk);
        
        // Test case 2: All zeros
        send_uart_packet(24'h0);
        wait(m_valid);
        repeat(10) @(posedge clk);
        
        // Test case 3: All ones
        send_uart_packet(24'hFFFFFF);
        wait(m_valid);
        repeat(10) @(posedge clk);
        
        // Test case 4: Random data with glitches
        repeat(3) begin
            automatic logic [W_OUT-1:0] random_data = $random();
            fork
                send_uart_packet(random_data);
                begin
                    repeat($urandom_range(5,10)) @(posedge clk);
                    add_glitch($urandom_range(1,3));
                end
            join
            wait(m_valid);
            repeat(10) @(posedge clk);
        end
        
        // Test case 5: Back-to-back transmissions
        repeat(3) begin
            automatic logic [W_OUT-1:0] random_data = $random();
            send_uart_packet(random_data);
            wait(m_valid);
        end
        
        // End simulation
        repeat(100) @(posedge clk);
        $display("Simulation completed successfully!");
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #1_000_000 $error("Simulation timeout!");
        $finish;
    end
    
    // Monitor process
    always @(posedge clk) begin
        if (m_valid) begin
            $display("Time=%0t: Received data = 0x%h", $time, m_data);
        end
    end
    
    // Error injection control - can be controlled via command line
    bit enable_error_injection;
    initial enable_error_injection = 0;  // Can be overridden from command line
    