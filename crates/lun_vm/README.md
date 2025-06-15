# Virtual Machine Reference

The (new) Virtual Machine reference.

The VM is in 64bit, so the word length is 64bit, `XLEN = 64`

## Registers

Every register is 64 bit wide.

### General purpose registers

registers are named `x0` to `x15`.

ABI name:
```
zr  a0  a1  a2
a3  a4  t0  t1
t2  t3  s0  s1
s2  s3  fp  sp
```

```
| regs |       description       | saver  |
| zr   | hard-wired zero         |   X    |
| a0-1 | argument / return value | caller |
| a2-4 | argument                | caller |
| t0-3 | temporary               | caller |
| s0-3 | saved registers         | callee |
| fp   | frame pointer           | callee |
| sp   | stack pointer           | callee |
```

### Special Register:

```
pc -> program counter
```

## Instructions

### Arithmetic & Logic

```
- add.funct rd, rs1, rs2
  -> opcode = 0
  => x[rd] = x[rs1] + x[rs2]

- sub.funct rd, rs1, rs2
  -> opcode = 1
  => x[rd] = x[rs1] - x[rs2]

- mul.funct rd, rs1, rs2
  -> opcode = 2
  => x[rd] = x[rs1] * x[rs2]

- div.funct rd, rs1, rs2
  -> opcode = 3
  => x[rd] = x[rs1] / x[rs2]

- rem.funct rd, rs1, rs2
  -> opcode = 4
  => x[rd] = x[rs1] % x[rs2]

- clt.funct rd, rs1, rs2
  -> opcode = 5
  => x[rd] = x[rs1] < x[rs2]

- cge.funct rd, rs1, rs2
  -> opcode = 6
  => x[rd] = x[rs1] >= x[rs2]

- ceq.funct rd, rs1, rs2
  -> opcode = 7
  => x[rd] = x[rs1] == x[rs2]

- cne.funct rd, rs1, rs2
  -> opcode = 8
  => x[rd] = x[rs1] != x[rs2]

- and.funct rd, rs1, rs2
  -> opcode = 9
  => x[rd] = x[rs1] and x[rs2]

- or.funct rd, rs1, rs2
  -> opcode = 10
  => x[rd] = x[rs1] or x[rs2]

- xor.funct rd, rs1, rs2
  -> opcode = 11
  => x[rd] = x[rs1] xor x[rs2]

WHERE funct is:
 funct | 4b val |     description     | instruction example |
   X   |   0    | integer arithmetics | add s0, t0, t1      |
  f16  |   1    | f16 arithmetics     | add.f16 s0, t0, t1  |
  f32  |   2    | f32 arithmetics     | add.f32 s0, t0, t1  |
  f64  |   3    | f64 arithmetics     | add.f64 s0, t0, t1  |

  LAYOUT :

OPCODE | funct | rd | rs1 | rs2
  8b   |  4b   | 4b | 4b  | 4b
=> 24 bits total
```

### Branching

```
- call imm32
  -> opcode = 12
  -> layout = opcode | imm = 40b
  -> imm32 is 32b immediate
  => X[sp] -= XLEN / 8; M[x[sp]] = pc + 5; pc = imm32

- ret
  -> opcode = 13
  -> layout = opcode = 8b
  => pc = M[x[sp]] ; x[sp] += XLEN/8

- jze rs2, offset(rs1)
  -> opcode = 14
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if x[rs] == 0 then pc += sext(offset)

- beq rs1, rs2, offset
  -> opcode = 15
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if x[rs1] == x[rs2] then pc += sext(offset)

- bne rs1, rs2, offset
  -> opcode = 16
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if x[rs1] != x[rs2] then pc += sext(offset)

- blt rs1, rs2, offset
  -> opcode = 17
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if x[rs1] < x[rs2] then pc += sext(offset)

- bge rs1, rs2, offset
  -> opcode = 18
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if x[rs1] >= x[rs2] then pc += sext(offset)
```

### Memory

```
- ld.b rd, offset(rs)
  -> opcode = 19
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => x[rd] = M[x[rs] + sext(offset)][7:0]
- ld.h rd, offset(rs)
  -> opcode = 20
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => x[rd] = M[x[rs] + sext(offset)][15:0]
- ld.w rd, offset(rs)
  -> opcode = 21
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => x[rd] = M[x[rs] + sext(offset)][31:0]
- ld.d rd, offset(rs)
  -> opcode = 22
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => x[rd] = M[x[rs] + sext(offset)][63:0]


- st.b rs2, offset(rs1)
  -> opcode = 23
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[x[rs1] + sext(offset)] = x[rs2][7:0]

- st.h rs2, offset(rs1)
  -> opcode = 24
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[x[rs1] + sext(offset)] = x[rs2][15:0]

- st.w rs2, offset(rs1)
  -> opcode = 25
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[x[rs1] + sext(offset)] = x[rs2][31:0]

- st.d rs2, offset(rs1)
  -> opcode = 26
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[x[rs1] + sext(offset)] = x[rs2][63:0]
```

### Moves

```
- li.b rd, imm(rs)
  -> opcode = 27
  -> layout = opcode | rs | rs1 | imm = 24b
  -> offset is a 8b immediate
  => x[rd] = imm[7:0]

- li.h rd, imm(rs)
  -> opcode = 28
  -> layout = opcode | rs | rs1 | imm = 32b
  -> offset is a 16b immediate
  => x[rd] = imm[15:0]

- li.w rd, imm(rs)
  -> opcode = 29
  -> layout = opcode | rs | rs1 | imm = 48b
  -> offset is a 32b immediate
  => x[rd] = imm[31:0]

- li.d rd, imm(rs)
  -> opcode = 30
  -> layout = opcode | rs | rs1 | imm = 80b
  -> offset is a 64b immediate
  => x[rd] = imm[63:0]

- mov rd, rs
  -> opcode = 31
  -> layout = opcode | rd | rs = 16b
  => x[rd] = rs
```

### Stack

```
- push rs
  -> opcode = 32
  -> layout = opcode | 0000 | rs = 16b
  => x[sp] = x[sp] - XLEN/8 ; M[x[sp]] = x[rs]
- pop rd
  -> opcode = 33
  -> layout = opcode | 0000 | rd = 16b
  => x[rd] = M[x[sp]] ; x[sp] += XLEN/8
```

## Bus & Memory

Memory Map
```
┌─────────┐
│         │ 0
│ special │
│   ???   │ 255
├─────────┤
│         │ program_start = 256
┊         ┊
┊ program ┊
┊         ┊
│   R-X   │ program_end = program_start + program_size
├─────────┤
│         │ stack_top = program_end + 1
┊         ┊
┊  stack  ┊
┊         ┊
│   RW-   │ stack_bottom = stack_top + stack_size
├─────────┤
│         │ canary_start = stack_bottom + 1
┊         ┊
┊ canary  ┊ 1024 bytes that are un accessible, it helps to catch stack overflow
┊         ┊
│   ---   │ canary_end = canary_start + 1024
├─────────┤
│         │ heap_base = canary_end + 1
┊         ┊
┊  heap   ┊
┊         ┊
│   ???   │
└─────────┘
```

`special`, `program`, `stack`, `cannary` `heap` are memory regions, those are
protected through protections. Read, Write and eXecute are the protections, and
each region as it's protection represented as RWX (you can do everything) or ---
(you can do nothing), or ??? when the protection is more complicated than that.

`special` has `???` because every address has its own protection.

`canary` is a 1024 bytes wide region of memory between the `stack` and the
`heap`, used to protect against most of the stack overflows and detect them
easier.

`heap` has `???` because the heap grows in regions and so every region have
their own protections, TODO: not sure about how exactly the heap would work
though.

### Special

```
addr   prot   usage
-----------------
0      ---    null pointer
...    ---    reserved
```

### Stack

The stack is a descending stack, it's bottom is defined as `stack_bottom`, the
stack cannot grow and the `stack_size` must be known before executing the
program.

### Program

The program size is the size of all the bytecode, it cannot grow, this region
is readonly and executable obviously.

### Heap

TODO: idk how it could work because we need to support freeing of memory, with
a garbage collector i think, but this heap thingy could not be the solution.
