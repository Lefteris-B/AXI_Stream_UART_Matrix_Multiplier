module skid_buffer #(
    parameter int WIDTH = 8
) (
    input  logic              clk,
    input  logic              rst_n,
    
    // Slave interface
    input  logic              s_valid,
    output logic              s_ready,
    input  logic [WIDTH-1:0]  s_data,
    
    // Master interface
    output logic              m_valid,
    input  logic              m_ready,
    output logic [WIDTH-1:0]  m_data
);
    // Main pipeline registers
    logic [WIDTH-1:0] pipe_data;
    logic             pipe_valid;
    
    // Skid buffer registers
    logic [WIDTH-1:0] skid_data;
    logic             skid_valid;
    
    // Flow control
    wire pipe_stall = m_valid && !m_ready;
    wire pipe_transfer = m_valid && m_ready;
    wire input_transfer = s_valid && s_ready;
    
    // Ready when skid buffer is empty
    assign s_ready = !skid_valid;
    
    // Data path
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_data <= '0;
            skid_data <= '0;
        end else begin
            // Main pipeline data
            if (input_transfer) begin
                pipe_data <= s_data;
            end
            
            // Skid buffer data
            if (input_transfer && pipe_stall) begin
                skid_data <= s_data;
            end
        end
    end
    
    // Control path
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pipe_valid <= 1'b0;
            skid_valid <= 1'b0;
        end else begin
            // Main pipeline valid control
            if (pipe_transfer) begin
                pipe_valid <= skid_valid ? 1'b1 : input_transfer;
            end else if (!pipe_stall) begin
                pipe_valid <= input_transfer;
            end
            
            // Skid buffer valid control
            if (pipe_transfer) begin
                skid_valid <= 1'b0;
            end else if (input_transfer && pipe_stall) begin
                skid_valid <= 1'b1;
            end
        end
    end
    
    // Output multiplexing
    assign m_valid = pipe_valid;
    assign m_data = pipe_data;

endmodule