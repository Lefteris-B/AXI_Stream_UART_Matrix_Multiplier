module axis_matvec_mul #(
    parameter R=8, C=8, W_X=8, W_K=8,
    localparam W_Y = W_X + W_K + $clog2(C)
)(
    input  logic clk, rstn,
    output logic s_axis_kx_tready,
    input  logic s_axis_kx_tvalid,
    input  logic [R*C*W_K + C*W_X -1:0] s_axis_kx_tdata,
    input  logic m_axis_y_tready,
    output logic m_axis_y_tvalid,
    output logic [R*W_Y-1:0] m_axis_y_tdata
);
    // State machine
    typedef enum logic [2:0] {
        IDLE,
        LOAD_DATA,
        COMPUTING,
        RESULT_READY
    } state_t;
    
    state_t state, next_state;

    // Internal registers
    logic [R-1:0][C-1:0][W_K-1:0] k_reg;
    logic [C-1:0][W_X-1:0] x_reg;
    logic [R*W_Y-1:0] y_reg;
    logic computing;
    logic [$clog2(C+2)-1:0] compute_counter;

    // State register
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Matrix-vector multiplier instance
    matvec_mul #(
        .R(R), .C(C), .W_X(W_X), .W_K(W_K)
    ) MATVEC (
        .clk(clk),
        .cen(computing),
        .k(k_reg),
        .x(x_reg),
        .y(y_reg)
    );

    // Next state logic
    always_comb begin
        next_state = state;
        case (state)
            IDLE: 
                if (s_axis_kx_tvalid && s_axis_kx_tready)
                    next_state = LOAD_DATA;
            
            LOAD_DATA:
                next_state = COMPUTING;
            
            COMPUTING: 
                if (compute_counter == C+1)
                    next_state = RESULT_READY;
            
            RESULT_READY:
                if (m_axis_y_tready)
                    next_state = IDLE;
        endcase
    end

    // Control and data path logic
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            k_reg <= '0;
            x_reg <= '0;
            computing <= 1'b0;
            compute_counter <= '0;
            m_axis_y_tvalid <= 1'b0;
            m_axis_y_tdata <= '0;
        end else begin
            case (state)
                IDLE: begin
                    compute_counter <= '0;
                    computing <= 1'b0;
                    if (s_axis_kx_tvalid && s_axis_kx_tready) begin
                        // Load data into registers
                        for (int r = 0; r < R; r++) begin
                            for (int c = 0; c < C; c++) begin
                                k_reg[r][c] <= s_axis_kx_tdata[(r*C + c)*W_K +: W_K];
                            end
                        end
                        for (int c = 0; c < C; c++) begin
                            x_reg[c] <= s_axis_kx_tdata[R*C*W_K + c*W_X +: W_X];
                        end
                    end
                end

                LOAD_DATA: begin
                    computing <= 1'b1;
                end

                COMPUTING: begin
                    compute_counter <= compute_counter + 1;
                    if (compute_counter == C+1) begin
                        m_axis_y_tdata <= y_reg;
                        m_axis_y_tvalid <= 1'b1;
                        computing <= 1'b0;
                    end
                end

                RESULT_READY: begin
                    if (m_axis_y_tready) begin
                        m_axis_y_tvalid <= 1'b0;
                    end
                end
            endcase
        end
    end

    // Ready signal generation
    assign s_axis_kx_tready = (state == IDLE);

    // Debug signals
    `ifdef SIMULATION
        // State transitions
        always @(state) begin
            $display("Time=%0t: AXIS_MVM state changed to %s", $time, state.name());
        end

        // Data transfers
        always @(posedge clk) begin
            if (s_axis_kx_tvalid && s_axis_kx_tready)
                $display("Time=%0t: AXIS_MVM received input data", $time);
            if (state == COMPUTING && compute_counter == 0)
                $display("Time=%0t: AXIS_MVM started computation", $time);
            if (m_axis_y_tvalid && m_axis_y_tready)
                $display("Time=%0t: AXIS_MVM output data=%h", $time, m_axis_y_tdata);
        end
    `endif

endmodule