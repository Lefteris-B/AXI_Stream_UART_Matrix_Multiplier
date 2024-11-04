module matvec_mul_tb;
    // Test parameters
    localparam int R     = 4;    // Smaller size for easier verification
    localparam int C     = 4;
    localparam int W_X   = 8;
    localparam int W_K   = 8;
    localparam int W_M   = W_X + W_K;
    localparam int W_Y   = W_M + $clog2(C);
    localparam int DEPTH = $clog2(C);
    localparam int LATENCY = DEPTH + 1;  // Multiply stage + adder tree stages

    // Maximum and minimum values for W_K and W_X bit widths
    localparam logic signed [W_K-1:0] MAX_K =  (1 << (W_K-1)) - 1;
    localparam logic signed [W_K-1:0] MIN_K = -(1 << (W_K-1));
    localparam logic signed [W_X-1:0] MAX_X =  (1 << (W_X-1)) - 1;
    localparam logic signed [W_X-1:0] MIN_X = -(1 << (W_X-1));

    // DUT signals
    logic                                 clk;
    logic                                 cen;
    logic signed [R-1:0][C-1:0][W_K-1:0] k;
    logic signed        [C-1:0][W_X-1:0] x;
    logic signed        [R-1:0][W_Y-1:0] y;

    // Testbench signals
    logic signed [R-1:0][W_Y-1:0] expected_y;
    int                           test_number;
    logic                         test_in_progress;
    
    // Queue to store input data for checking against delayed output
    logic signed [R-1:0][C-1:0][W_K-1:0] k_queue[$];
    logic signed        [C-1:0][W_X-1:0] x_queue[$];

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // DUT instantiation
    matvec_mul #(
        .R(R),
        .C(C),
        .W_X(W_X),
        .W_K(W_K)
    ) dut (.*);

    // VCD dump
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, matvec_mul_tb);
    end

    // Reference model for matrix-vector multiplication
    function automatic logic signed [R-1:0][W_Y-1:0] compute_expected(
        input logic signed [R-1:0][C-1:0][W_K-1:0] k_in,
        input logic signed        [C-1:0][W_X-1:0] x_in
    );
        logic signed [R-1:0][W_Y-1:0] result;
        logic signed [W_Y-1:0] sum;
        
        for (int r = 0; r < R; r++) begin
            sum = '0;
            for (int c = 0; c < C; c++) begin
                sum += $signed(k_in[r][c]) * $signed(x_in[c]);
            end
            result[r] = sum;
        end
        return result;
    endfunction

    // Task to apply a test vector and store expected result
    task automatic apply_test(
        input logic signed [R-1:0][C-1:0][W_K-1:0] k_test,
        input logic signed        [C-1:0][W_X-1:0] x_test
    );
        @(posedge clk);
        cen <= 1'b1;
        k <= k_test;
        x <= x_test;
        k_queue.push_back(k_test);
        x_queue.push_back(x_test);
        test_in_progress <= 1'b1;
        @(posedge clk);
        cen <= 1'b0;
    endtask

    // Monitor for checking results
    always @(posedge clk) begin
        if (test_in_progress && k_queue.size() > 0 && $time > 100) begin
            if (k_queue.size() == LATENCY) begin
                automatic logic signed [R-1:0][C-1:0][W_K-1:0] k_check = k_queue.pop_front();
                automatic logic signed        [C-1:0][W_X-1:0] x_check = x_queue.pop_front();
                automatic logic signed        [R-1:0][W_Y-1:0] y_expected = compute_expected(k_check, x_check);
                
                for (int r = 0; r < R; r++) begin
                    assert (y[r] === y_expected[r]) else begin
                        $error("Test %0d, Row %0d: Mismatch! Expected: %0h, Got: %0h", 
                               test_number, r, y_expected[r], y[r]);
                    end
                end
            end
        end
    end   
   // Test stimulus
    initial begin
        // Initialize
        test_number = 0;
        test_in_progress = 0;
        cen = 0;
        k = '0;
        x = '0;
        k_queue.delete();
        x_queue.delete();

        // Reset state
        repeat(5) @(posedge clk);
        
        // Wait for initial zero outputs
        cen = 1'b0;
        repeat(10) @(posedge clk);
        
        // Start tests
        test_in_progress = 1;

        // Test 1: Identity matrix
        test_number = 1;
        begin
            logic signed [R-1:0][C-1:0][W_K-1:0] k_identity;
            logic signed        [C-1:0][W_X-1:0] x_test;
            
            for (int i = 0; i < R; i++) begin
                for (int j = 0; j < C; j++) begin
                    k_identity[i][j] = (i == j) ? 8'sd1 : 8'sd0;
                end
            end
            for (int i = 0; i < C; i++) begin
                x_test[i] = 8'sd1;
            end
            
            apply_test(k_identity, x_test);
            repeat(LATENCY + 2) @(posedge clk);
        end

        // Subsequent tests...
        
        // Wait for pipeline to flush
        cen = 1'b0;
        repeat(LATENCY + 5) @(posedge clk);
        test_in_progress = 0;

        // End simulation
        repeat(5) @(posedge clk);
        $display("All tests completed!");
        $finish;
    end

    // Modified assertions
    property output_width_check;
        @(posedge clk)
        $bits(y[0]) >= W_X + W_K + $clog2(C);
    endproperty

    property clock_enable_check;
        @(posedge clk) disable iff (!test_in_progress)
        !cen && $stable(cen) |=> $stable(y);
    endproperty

    property input_stability_check;
        @(posedge clk) disable iff (!test_in_progress)
        (cen && $stable(cen)) |-> $stable(k) && $stable(x);
    endproperty

    sequence zero_inputs_seq;
        (!cen && k == '0 && x == '0)[*(LATENCY+1)];
    endsequence
    
    property zero_output_check;
        @(posedge clk) disable iff (test_in_progress)
        zero_inputs_seq |-> y == '0;
    endproperty

    property verify_latency;
        @(posedge clk) disable iff (!test_in_progress)
        $rose(cen) |-> ##[LATENCY:LATENCY+1] !$stable(y);
    endproperty

    // Assert all properties
    assert_output_width:        assert property(output_width_check);
    assert_clock_enable:        assert property(clock_enable_check);
    assert_input_stability:     assert property(input_stability_check);
    assert_zero_output:         assert property(zero_output_check);
    assert_latency:            assert property(verify_latency);

    // Coverage
    covergroup matvec_coverage @(posedge clk);
        option.per_instance = 1;
        option.name = "matvec_coverage";

        // Cover different input patterns for matrix k
        k_values: coverpoint k[0][0] {
            bins zero = {0};
            bins small_pos = {[1:32]};
            bins small_neg = {[-32:-1]};
            bins large_pos = {[33:MAX_K]};
            bins large_neg = {[MIN_K:-33]};
            bins max_val = {MAX_K};
            bins min_val = {MIN_K};
        }

        // Cover different input patterns for vector x
        x_values: coverpoint x[0] {
            bins zero = {0};
            bins small_pos = {[1:32]};
            bins small_neg = {[-32:-1]};
            bins large_pos = {[33:MAX_X]};
            bins large_neg = {[MIN_X:-33]};
            bins max_val = {MAX_X};
            bins min_val = {MIN_X};
        }

        // Cover clock enable transitions
        cen_trans: coverpoint cen {
            bins transitions = (0 => 1), (1 => 0);
        }

        // Cross coverage
        k_x_cross: cross k_values, x_values;
    endgroup

    matvec_coverage cov = new();

endmodule