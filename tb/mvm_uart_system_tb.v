`timescale 1ns/1ps

module mvm_uart_system_tb;
    // Test parameters
    localparam CLOCKS_PER_PULSE = 4; // Reduced for simulation
    localparam BITS_PER_WORD    = 8;
    localparam R = 8;
    localparam C = 8;
    localparam W_X = 4;
    localparam W_K = 3;
    localparam W_Y_OUT = 32;
    
    // Derive bus widths
    localparam W_BUS_KX = R*C*W_K + C*W_X;
    localparam W_BUS_Y  = R*W_Y_OUT;
    localparam W_Y = W_X + W_K + $clog2(C);
    localparam NUM_WORDS_RX = (W_BUS_KX + BITS_PER_WORD - 1) / BITS_PER_WORD;
    localparam NUM_WORDS_TX = (W_BUS_Y + BITS_PER_WORD - 1) / BITS_PER_WORD;
    
    // DUT signals
    logic clk = 0;
    logic rstn;
    logic rx;
    logic tx;

    // Test vectors
    logic [R-1:0][C-1:0][W_K-1:0] test_k;
    logic [C-1:0][W_X-1:0] test_x;
    logic [R-1:0][W_Y_OUT-1:0] expected_y;
    logic [R-1:0][W_Y_OUT-1:0] received_y;

    // Debug signals
    logic [W_BUS_KX-1:0] debug_send_data;
    logic [W_BUS_Y-1:0] debug_received_data;

    // Clock generation
    always #5 clk = ~clk;

    // DUT instantiation
    mvm_uart_system #(
        .CLOCKS_PER_PULSE(CLOCKS_PER_PULSE),
        .BITS_PER_WORD(BITS_PER_WORD),
        .R(R),
        .C(C),
        .W_X(W_X),
        .W_K(W_K),
        .W_Y_OUT(W_Y_OUT)
    ) DUT (
        .clk(clk),
        .rstn(rstn),
        .rx(rx),
        .tx(tx)
    );

    // VCD dump
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, mvm_uart_system_tb);
    end

    // Task to send byte over UART with debug
    task automatic send_uart_byte(input logic [7:0] data);
        $display("Sending UART byte: %h", data);
        rx = 0; // Start bit
        #(CLOCKS_PER_PULSE*10);
        
        for(int i = 0; i < 8; i++) begin
            rx = data[i];
            #(CLOCKS_PER_PULSE*10);
        end
        
        rx = 1; // Stop bit
        #(CLOCKS_PER_PULSE*10);
    endtask

    // Task to receive byte over UART with debug
    task automatic receive_uart_byte(output logic [7:0] data);
        @(negedge tx);  // Wait for start bit
        $display("Receiving UART byte starting");
        #(CLOCKS_PER_PULSE*15); // Wait to middle of first data bit
        
        for(int i = 0; i < 8; i++) begin
            data[i] = tx;
            #(CLOCKS_PER_PULSE*10);
        end
        
        wait(tx == 1); // Wait for stop bit
        #(CLOCKS_PER_PULSE*10);
        $display("Received UART byte: %h", data);
    endtask

    // Test stimulus
    initial begin
        // Initialize
        rstn = 0;
        rx = 1;
        test_k = '0;
        test_x = '0;
        debug_send_data = '0;
        debug_received_data = '0;
        
        // Reset sequence
        repeat(20) @(posedge clk);
        rstn = 1;
        repeat(20) @(posedge clk);
        
        // Test case 1: Simple pattern
        for(int i = 0; i < R; i++) begin
            for(int j = 0; j < C; j++) begin
                test_k[i][j] = (i == j) ? 1 : 0;
                $display("test_k[%0d][%0d] = %0d", i, j, test_k[i][j]);
            end
        end
        
        for(int i = 0; i < C; i++) begin
            test_x[i] = i + 1;
            $display("test_x[%0d] = %0d", i, test_x[i]);
        end
        
        // Pack and send data
        debug_send_data = '0;
        for(int r = 0; r < R; r++) begin
            for(int c = 0; c < C; c++) begin
                debug_send_data[((r*C + c)*W_K) +: W_K] = test_k[r][c];
            end
        end
        for(int c = 0; c < C; c++) begin
            debug_send_data[(R*C*W_K + c*W_X) +: W_X] = test_x[c];
        end
        
        $display("Sending data packet: %h", debug_send_data);
        
        // Send bytes
        for(int i = 0; i < NUM_WORDS_RX; i++) begin
            logic [7:0] byte_to_send;
            byte_to_send = debug_send_data[i*8 +: 8];
            send_uart_byte(byte_to_send);
            @(posedge clk);
        end
        
        // Wait for processing
        $display("Waiting for processing...");
        repeat(1000) @(posedge clk);
        
        // Check internal signals
        $display("AXIS_MVM signals:");
        $display("s_axis_kx_tvalid: %b", DUT.AXIS_MVM.s_axis_kx_tvalid);
        $display("s_axis_kx_tready: %b", DUT.AXIS_MVM.s_axis_kx_tready);
        $display("m_axis_y_tvalid: %b", DUT.AXIS_MVM.m_axis_y_tvalid);
        $display("m_axis_y_tready: %b", DUT.AXIS_MVM.m_axis_y_tready);
        
        // Wait for and receive results
        $display("Waiting for results...");
        fork
            begin
                for(int i = 0; i < NUM_WORDS_TX; i++) begin
                    logic [7:0] received_byte;
                    receive_uart_byte(received_byte);
                    debug_received_data[i*8 +: 8] = received_byte;
                end
            end
            begin
                repeat(10000) @(posedge clk);
                $display("Timeout waiting for results!");
                $finish;
            end
        join_any
        
        $display("Final received data: %h", debug_received_data);
        
        // Unpack and check results
        for(int r = 0; r < R; r++) begin
            received_y[r] = debug_received_data[r*W_Y_OUT +: W_Y_OUT];
            $display("Row %0d result: %h", r, received_y[r]);
        end
        
        repeat(100) @(posedge clk);
        $finish;
    end

    // Debug monitors
    always @(posedge clk) begin
        if (DUT.UART_RX.m_valid)
            $display("UART_RX valid, data=%h", DUT.UART_RX.m_data);
        if (DUT.AXIS_MVM.m_axis_y_tvalid && DUT.AXIS_MVM.m_axis_y_tready)
            $display("AXIS_MVM output valid, data=%h", DUT.AXIS_MVM.m_axis_y_tdata);
        if (DUT.UART_TX.s_valid && DUT.UART_TX.s_ready)
            $display("UART_TX input valid, data=%h", DUT.UART_TX.s_data);
    end

    // Assertions
    property reset_behavior;
        @(posedge clk) !rstn |=> !DUT.AXIS_MVM.m_axis_y_tvalid;
    endproperty
    assert property(reset_behavior) else
        $error("Reset behavior violation");

    property uart_rx_protocol;
        @(posedge clk) disable iff(!rstn)
        $fell(rx) |-> ##[1:(CLOCKS_PER_PULSE*10-1)] $rose(rx);
    endproperty
    assert property(uart_rx_protocol) else
        $error("UART RX protocol violation");

    property axis_handshake;
        @(posedge clk) disable iff(!rstn)
        DUT.AXIS_MVM.s_axis_kx_tvalid && !DUT.AXIS_MVM.s_axis_kx_tready |=>
        DUT.AXIS_MVM.s_axis_kx_tvalid;
    endproperty
    assert property(axis_handshake) else
        $error("AXI-Stream handshake violation");

    // Comprehensive debug monitor
    initial begin
        $monitor("Time=%0t rstn=%0b rx=%0b tx=%0b UART_RX_valid=%b AXIS_valid=%b UART_TX_ready=%b",
                 $time, rstn, rx, tx,
                 DUT.UART_RX.m_valid,
                 DUT.AXIS_MVM.m_axis_y_tvalid,
                 DUT.UART_TX.s_ready);
    end

endmodule