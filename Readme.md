# Pipelined Matrix-Vector Multiplication with UART Interface

## Overview
This project implements a pipelined matrix-vector multiplication (MVM) system with UART communication interface. The design is optimized for FPGA implementation and features a fully pipelined datapath with AXI-Stream interfaces.

##
Simulation and testbench: [EDA Playground - Digital Logic Design](https://edaplayground.com/x/kaBL)


## Features
- Configurable matrix dimensions (default 8x8)
- Parameterized data widths
- UART communication interface (configurable baud rate)
- AXI-Stream compliant interfaces
- Pipelined architecture for high throughput
- Full handshaking protocol support

## Architecture
```
          ┌──────────┐      ┌───────────────┐      ┌──────────┐
UART_RX   │  AXIS    │      │   Pipelined   │      │  UART    │
─────────►│  MVM     ├─────►│   Matrix-Vec  ├─────►│   TX     ├─────►
          │Interface │      │     Mult      │      │         │
          └──────────┘      └───────────────┘      └──────────┘
```

## Modules
1. `mvm_uart_system`: Top-level system integration
2. `axis_matvec_mul`: AXI-Stream wrapper for matrix multiplication
3. `matvec_mul`: Core matrix-vector multiplication engine
4. `uart_rx`: UART receiver with data buffering
5. `uart_tx`: UART transmitter with flow control
6. `skid_buffer`: AXI-Stream buffer for flow control

## Parameters
- `R`: Number of matrix rows (default: 8)
- `C`: Number of matrix columns (default: 8)
- `W_X`: Input vector element width (default: 4)
- `W_K`: Matrix element width (default: 3)
- `W_Y_OUT`: Output width (default: 32)
- `CLOCKS_PER_PULSE`: UART clock division ratio

## Interface
### Input Format
- Matrix K: R×C elements of W_K bits each
- Vector X: C elements of W_X bits each
- Data sent over UART in row-major order

### Output Format
- Vector Y: R elements of W_Y_OUT bits each
- Sign-extended results
- Transmitted over UART sequentially

## Getting Started
1. Clone the repository
2. Configure parameters in top-level module as needed
3. Synthesize for target FPGA
4. Connect UART interface (default 9600 baud)

## Simulation
```bash
# Run simulation with provided testbench
xrun -sv mvm_uart_system_tb.sv
```

## Example Usage
```verilog
// Instantiate top module
mvm_uart_system #(
    .R(8),
    .C(8),
    .W_X(4),
    .W_K(3),
    .W_Y_OUT(32)
) mvm_inst (
    .clk(clk),
    .rstn(rstn),
    .rx(uart_rx),
    .tx(uart_tx)
);
```

## Performance
- Pipelined operation: One result per clock cycle after initial latency
- Latency: log2(C) + 1 cycles for computation
- UART overhead: Determined by baud rate and data width

## Testing
The design includes:
- SystemVerilog testbench
- Self-checking assertions
- Protocol verification
- Coverage monitoring

