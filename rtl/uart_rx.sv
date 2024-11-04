module uart_rx #(
    parameter CLOCKS_PER_PULSE = 4,
             BITS_PER_WORD    = 8,
             W_OUT            = 24,
    localparam NUM_WORDS      = (W_OUT + BITS_PER_WORD - 1) / BITS_PER_WORD,
    localparam SAMPLE_POINT   = CLOCKS_PER_PULSE/2
)(
    input  logic clk,
    input  logic rstn,
    input  logic rx,
    output logic m_valid,
    output logic [W_OUT-1:0] m_data
);
    // State definitions
    typedef enum logic [2:0] {
        IDLE,
        START,
        DATA,
        STOP,
        ACCUMULATE
    } state_t;

    // Registers
    state_t state;
    logic [$clog2(CLOCKS_PER_PULSE)-1:0] clock_counter;
    logic [$clog2(BITS_PER_WORD)-1:0] bit_counter;
    logic [$clog2(NUM_WORDS)-1:0] word_counter;
    logic [BITS_PER_WORD-1:0] shift_reg;
    logic [W_OUT-1:0] data_accumulator;

    // Synchronize RX input
    logic rx_meta, rx_sync;
    always_ff @(posedge clk) begin
        {rx_sync, rx_meta} <= {rx_meta, rx};
    end

    // Main state machine
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= IDLE;
            clock_counter <= '0;
            bit_counter <= '0;
            word_counter <= '0;
            shift_reg <= '0;
            data_accumulator <= '0;
            m_valid <= 1'b0;
            m_data <= '0;
        end else begin
            m_valid <= 1'b0;
            
            case (state)
                IDLE: begin
                    if (!rx_sync) begin
                        state <= START;
                        clock_counter <= '0;
                        if (word_counter == '0)
                            data_accumulator <= '0;
                    end
                end

                START: begin
                    if (clock_counter == SAMPLE_POINT) begin
                        if (!rx_sync) begin
                            state <= DATA;
                            clock_counter <= '0;
                            bit_counter <= '0;
                        end else
                            state <= IDLE;
                    end else
                        clock_counter <= clock_counter + 1;
                end

                DATA: begin
                    if (clock_counter == SAMPLE_POINT) begin
                        shift_reg <= {rx_sync, shift_reg[BITS_PER_WORD-1:1]};
                        bit_counter <= bit_counter + 1;
                        if (bit_counter == BITS_PER_WORD-1)
                            state <= STOP;
                    end
                    
                    if (clock_counter == CLOCKS_PER_PULSE-1)
                        clock_counter <= '0;
                    else
                        clock_counter <= clock_counter + 1;
                end

                STOP: begin
                    if (clock_counter == SAMPLE_POINT) begin
                        if (rx_sync) begin
                            state <= ACCUMULATE;
                            clock_counter <= '0;
                        end else
                            state <= IDLE;  // Framing error
                    end else
                        clock_counter <= clock_counter + 1;
                end

                ACCUMULATE: begin
                    data_accumulator[(word_counter*BITS_PER_WORD) +: BITS_PER_WORD] <= shift_reg;
                    word_counter <= word_counter + 1;
                    
                    if (word_counter == NUM_WORDS-1) begin
                        state <= IDLE;
                        word_counter <= '0;
                        m_valid <= 1'b1;
                        m_data <= {shift_reg, data_accumulator[W_OUT-BITS_PER_WORD-1:0]};
                    end else
                        state <= IDLE;
                end
            endcase
        end
    end

    // Debug information
    `ifdef SIMULATION
        always @(posedge clk) begin
            if (m_valid)
                $display("UART_RX: Complete word received, data=%h", m_data);
            if (state == ACCUMULATE)
                $display("UART_RX: Accumulated word %0d: %h", word_counter, shift_reg);
        end
    `endif

endmodule