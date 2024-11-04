module uart_tx #(
    parameter CLOCKS_PER_PULSE = 4,
             BITS_PER_WORD    = 8,
             W_OUT            = 256,
             STOP_BITS        = 1,
    
    localparam NUM_WORDS   = (W_OUT + BITS_PER_WORD - 1) / BITS_PER_WORD,
    localparam TOTAL_BITS  = BITS_PER_WORD + 1 + STOP_BITS
)(
    input  logic clk,    
    input  logic rstn,   
    input  logic s_valid,
    input  logic [W_OUT-1:0] s_data,
    output logic s_ready,
    output logic tx
);
    // State machine
    typedef enum logic [2:0] {
        IDLE,
        LOAD,
        START,
        DATA,
        STOP,
        WAIT
    } state_t;

    // Registers
    state_t state;
    logic [$clog2(CLOCKS_PER_PULSE)-1:0] clock_counter;
    logic [$clog2(BITS_PER_WORD)-1:0] bit_counter;
    logic [$clog2(NUM_WORDS)-1:0] word_counter;
    logic [W_OUT-1:0] tx_data;
    logic [BITS_PER_WORD-1:0] current_byte;

    // Debug signals
    logic [31:0] total_bytes_sent;

    // State machine
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= IDLE;
            clock_counter <= '0;
            bit_counter <= '0;
            word_counter <= '0;
            tx_data <= '0;
            current_byte <= '0;
            tx <= 1'b1;
            s_ready <= 1'b1;
            total_bytes_sent <= '0;
        end else begin
            case (state)
                IDLE: begin
                    tx <= 1'b1;
                    s_ready <= 1'b1;
                    if (s_valid) begin
                        state <= LOAD;
                        tx_data <= s_data;
                        word_counter <= '0;
                        s_ready <= 1'b0;
                        $display("Time=%0t: UART_TX starting transmission of %0d bytes", $time, NUM_WORDS);
                    end
                end

                LOAD: begin
                    current_byte <= tx_data[word_counter*BITS_PER_WORD +: BITS_PER_WORD];
                    state <= START;
                    clock_counter <= '0;
                    $display("Time=%0t: UART_TX loading byte %0d: %h", $time, word_counter, 
                            tx_data[word_counter*BITS_PER_WORD +: BITS_PER_WORD]);
                end

                START: begin
                    tx <= 1'b0;
                    if (clock_counter == CLOCKS_PER_PULSE - 1) begin
                        state <= DATA;
                        clock_counter <= '0;
                        bit_counter <= '0;
                    end else begin
                        clock_counter <= clock_counter + 1;
                    end
                end

                DATA: begin
                    tx <= current_byte[bit_counter];
                    if (clock_counter == CLOCKS_PER_PULSE - 1) begin
                        clock_counter <= '0;
                        if (bit_counter == BITS_PER_WORD - 1) begin
                            state <= STOP;
                        end else begin
                            bit_counter <= bit_counter + 1;
                        end
                    end else begin
                        clock_counter <= clock_counter + 1;
                    end
                end

                STOP: begin
                    tx <= 1'b1;
                    if (clock_counter == CLOCKS_PER_PULSE - 1) begin
                        clock_counter <= '0;
                        total_bytes_sent <= total_bytes_sent + 1;
                        $display("Time=%0t: UART_TX sent byte %0d of %0d", $time, word_counter + 1, NUM_WORDS);
                        
                        if (word_counter == NUM_WORDS - 1) begin
                            state <= WAIT;
                            $display("Time=%0t: UART_TX transmission complete", $time);
                        end else begin
                            word_counter <= word_counter + 1;
                            state <= LOAD;
                        end
                    end else begin
                        clock_counter <= clock_counter + 1;
                    end
                end

                WAIT: begin
                    tx <= 1'b1;
                    if (clock_counter == CLOCKS_PER_PULSE - 1) begin
                        state <= IDLE;
                        s_ready <= 1'b1;
                    end else begin
                        clock_counter <= clock_counter + 1;
                    end
                end
            endcase
        end
    end

    // Additional debug monitoring
    `ifdef SIMULATION
        // Monitor state changes
        always @(state) begin
            $display("Time=%0t: UART_TX state changed to %s", $time, state.name());
        end

        // Monitor byte completion
        property byte_complete;
            @(posedge clk) disable iff(!rstn)
            (state == STOP && clock_counter == CLOCKS_PER_PULSE - 1) |->
            ##[1:CLOCKS_PER_PULSE] (state != STOP);
        endproperty
        assert property(byte_complete);

        // Monitor proper stop bit
        property stop_bit_high;
            @(posedge clk) disable iff(!rstn)
            (state == STOP) |-> tx == 1'b1;
        endproperty
        assert property(stop_bit_high);
    `endif

endmodule