`include "uart_tx.v"
`include "uart_rx.v"
`include "skid_buffer.v"
`include "matvec_mul.v"
`include "axis_matvec_mul.v"

module mvm_uart_system #(
    parameter int CLOCKS_PER_PULSE = 200_000_000/9600,
    parameter int BITS_PER_WORD    = 8,
    parameter int R       = 8,
    parameter int C       = 8,
    parameter int W_X     = 4,
    parameter int W_K     = 3,
    parameter int W_Y_OUT = 32,
    
    // Derived Parameters
    localparam int W_Y      = W_X + W_K + $clog2(C),
    localparam int W_BUS_KX = R*C*W_K + C*W_X,
    localparam int W_BUS_Y  = R*W_Y_OUT
)(
    input  logic clk,
    input  logic rstn,
    input  logic rx,
    output logic tx
);
    // Interface signals
    logic                  rx_valid, rx_ready;
    logic [W_BUS_KX-1:0]  rx_data;
    
    logic                  skid_valid, skid_ready;
    logic [W_BUS_KX-1:0]  skid_data;
    
    logic                  mvm_valid, mvm_ready;
    logic [R*W_Y-1:0]     mvm_data;
    
    logic                  tx_valid;
    logic                  tx_ready;
    logic [R*W_Y_OUT-1:0] tx_data;

    // Debug state tracking
    enum logic [2:0] {
        IDLE,
        RECEIVING,
        PROCESSING,
        TRANSMITTING,
        COMPLETE
    } state;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            state <= IDLE;
        end else begin
            case (state)
                IDLE: if (rx_valid) state <= RECEIVING;
                RECEIVING: if (skid_valid) state <= PROCESSING;
                PROCESSING: if (mvm_valid) state <= TRANSMITTING;
                TRANSMITTING: if (tx_ready && !tx_valid) state <= COMPLETE;
                COMPLETE: state <= IDLE;
            endcase
        end
    end

    // UART Receiver
    uart_rx #(
        .CLOCKS_PER_PULSE (CLOCKS_PER_PULSE),
        .BITS_PER_WORD    (BITS_PER_WORD),
        .W_OUT            (W_BUS_KX)
    ) UART_RX (
        .clk     (clk),
        .rstn    (rstn),
        .rx      (rx),
        .m_valid (rx_valid),
        .m_data  (rx_data)
    );

    // Skid buffer for UART RX -> AXIS_MVM interface
    skid_buffer #(
        .WIDTH (W_BUS_KX)
    ) UART_TO_MVM_SKID (
        .clk     (clk),
        .rst_n    (rstn),
        .s_valid (rx_valid),
        .s_ready (rx_ready),
        .s_data  (rx_data),
        .m_valid (skid_valid),
        .m_ready (skid_ready),
        .m_data  (skid_data)
    );

    // Matrix-Vector Multiplier
    axis_matvec_mul #(
        .R   (R),
        .C   (C),
        .W_X (W_X),
        .W_K (W_K)
    ) AXIS_MVM (
        .clk                (clk),
        .rstn               (rstn),
        .s_axis_kx_tready   (skid_ready),
        .s_axis_kx_tvalid   (skid_valid),
        .s_axis_kx_tdata    (skid_data),
        .m_axis_y_tready    (tx_ready),
        .m_axis_y_tvalid    (mvm_valid),
        .m_axis_y_tdata     (mvm_data)
    );

    // Output width conversion and sign extension
    genvar r;
    generate
        for (r = 0; r < R; r++) begin : g_output_conversion
            logic [W_Y-1:0] y_up;
            assign y_up = mvm_data[W_Y*(r+1)-1 : W_Y*r];
            assign tx_data[W_Y_OUT*(r+1)-1 : W_Y_OUT*r] = $signed(y_up);
        end
    endgenerate

    // UART Transmitter
    uart_tx #(
        .CLOCKS_PER_PULSE (CLOCKS_PER_PULSE),
        .BITS_PER_WORD    (BITS_PER_WORD),
        .W_OUT            (W_BUS_Y)
    ) UART_TX (
        .clk     (clk),
        .rstn    (rstn),
        .s_ready (tx_ready),
        .s_valid (mvm_valid),
        .s_data  (tx_data),
        .tx      (tx)
    );

    // Debug monitoring
    `ifdef SIMULATION
        always @(posedge clk) begin
            if (rx_valid && rx_ready)
                $display("Time=%0t: UART RX -> SKID transfer", $time);
            if (skid_valid && skid_ready)
                $display("Time=%0t: SKID -> MVM transfer, data=%h", $time, skid_data);
            if (mvm_valid && tx_ready)
                $display("Time=%0t: MVM -> UART TX transfer, data=%h", $time, mvm_data);
            
            case (state)
                IDLE:         $display("Time=%0t: State=IDLE", $time);
                RECEIVING:    $display("Time=%0t: State=RECEIVING", $time);
                PROCESSING:   $display("Time=%0t: State=PROCESSING", $time);
                TRANSMITTING: $display("Time=%0t: State=TRANSMITTING", $time);
                COMPLETE:     $display("Time=%0t: State=COMPLETE", $time);
            endcase
        end

        // Debug display of FSM state
        always @(state) begin
            $display("Time=%0t: FSM State changed to %s", $time, state.name());
        end
    `endif

    // Assertions
    property valid_stable_uart;
        @(posedge clk) disable iff(!rstn)
        rx_valid && !rx_ready |=> rx_valid;
    endproperty
    assert property(valid_stable_uart);

    property valid_stable_skid;
        @(posedge clk) disable iff(!rstn)
        skid_valid && !skid_ready |=> skid_valid;
    endproperty
    assert property(valid_stable_skid);

    property valid_stable_mvm;
        @(posedge clk) disable iff(!rstn)
        mvm_valid && !tx_ready |=> mvm_valid;
    endproperty
    assert property(valid_stable_mvm);

endmodule