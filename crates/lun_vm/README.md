# Virtual Machine Reference

The (new) Virtual Machine reference.

The VM is in 64bit, so the word length is 64bit, `WORD_LEN = 64`

## Registers

Every register is 64 bit wide.

### General purpose registers

```
rze  ra0  ra1  ra2
ra3  ra4  ra5  rt0
rt1  rt2  rt3  rt4
rt5  rfl  rfp  rsp
```

```
| regs  |       description       | saver  |
| rze   | hard-wired zero         |   X    |
| ra0-1 | argument / return value | caller |
| ra2-5 | argument                | caller |
| rt0-5 | temporary               | caller |
| rfl   | flag reg. see below     |   X    |
| rfp   | frame pointer           | callee |
| rsp   | stack pointer           | callee |
```

#### `rfl` Flags

```
0                                                            63
|OF|                         Reserved                         |

OF is a bit, when set to 1, the last arithmetic instruction overflowed,
             when set to 0, no overflow
```


### Special Registers:

```
pc -> program counter
```

## Instructions

### Arithmetic & Logic

```
- add.type rd, rs1, rs2
  -> opcode = 0
  => rd = rs1 + rs2

- sub.type rd, rs1, rs2
  -> opcode = 1
  => rd = rs1 - rs2

- mul.type rd, rs1, rs2
  -> opcode = 2
  => rd = rs1 * rs2

- div.type rd, rs1, rs2
  -> opcode = 3
  => rd = rs1 / rs2

- rem.type rd, rs1, rs2
  -> opcode = 4
  => rd = rs1 % rs2

- clt.type rd, rs1, rs2
  -> opcode = 5
  => rd = rs1 < rs2

- cge.type rd, rs1, rs2
  -> opcode = 6
  => rd = rs1 >= rs2

- ceq.type rd, rs1, rs2
  -> opcode = 7
  => rd = rs1 == rs2

- cne.type rd, rs1, rs2
  -> opcode = 8
  => rd = rs1 != rs2

- and.type rd, rs1, rs2
  -> opcode = 9
  => rd = rs1 and rs2

- or.type rd, rs1, rs2
  -> opcode = 10
  => rd = rs1 or rs2

- xor.type rd, rs1, rs2
  -> opcode = 11
  => rd = rs1 xor rs2

WHERE type is 4bit value:
0      -> u8
1      -> u16
2      -> u32
3      -> u64
4      -> i8
5      -> i16
6      -> i32
7      -> i64
8      -> f16
9      -> f32
10     -> f64
11..15 -> reserved

LAYOUT

OPCODE | type | rd | rs1 | rs2
  8b   |  4b  | 4b | 4b  | 4b
=> 24 bits total
```

### Branching

```
- call offset
  -> opcode = 12
  -> layout = opcode | imm = 40b
  -> offset is 32b immediate
  => rsp = rsp - WORD_LEN/8 ; M[rsp] = rs ; pc += sext(offset)

- ret
  -> opcode = 13
  -> layout = opcode = 8b
  => pc = M[rsp] ; rsp = rsp + WORD_LEN/8

- jze rs2, offset(rs1)
  -> opcode = 14
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if rs == 0 then pc += sext(offset)

- beq rs1, rs2, offset
  -> opcode = 15
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if rs1 == rs2 then pc += sext(offset)

- bne rs1, rs2, offset
  -> opcode = 16
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if rs1 != rs2 then pc += sext(offset)

- blt rs1, rs2, offset
  -> opcode = 17
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if rs1 < rs2 then pc += sext(offset)

- bge rs1, rs2, offset
  -> opcode = 18
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => if rs1 >= rs2 then pc += sext(offset)
```

### Memory

```
- ld.b rd, offset(rs)
  -> opcode = 19
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => rd = M[rs + sext(offset)][7:0]
- ld.h rd, offset(rs)
  -> opcode = 20
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => rd = M[rs + sext(offset)][15:0]
- ld.w rd, offset(rs)
  -> opcode = 21
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => rd = M[rs + sext(offset)][31:0]
- ld.d rd, offset(rs)
  -> opcode = 22
  -> layout = opcode | rd | rs | offset = 32b
  -> offset is a 16b immediate
  => rd = M[rs + sext(offset)][63:0]


- st.b rs2, offset(rs1)
  -> opcode = 23
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[rs1 + sext(offset)] = rs2[7:0]

- st.h rs2, offset(rs1)
  -> opcode = 24
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[rs1 + sext(offset)] = rs2[15:0]

- st.w rs2, offset(rs1)
  -> opcode = 25
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[rs1 + sext(offset)] = rs2[31:0]

- st.d rs2, offset(rs1)
  -> opcode = 26
  -> layout = opcode | rs1 | rs2 | offset = 32b
  -> offset is a 16b immediate
  => M[rs1 + sext(offset)] = rs2[63:0]
```

### Moves

```
- li.b rd, imm(rs)
  -> opcode = 27
  -> layout = opcode | rs | rs1 | imm = 24b
  -> offset is a 8b immediate
  => rd = imm[7:0]

- li.h rd, imm(rs)
  -> opcode = 28
  -> layout = opcode | rs | rs1 | imm = 32b
  -> offset is a 16b immediate
  => rd = imm[15:0]

- li.w rd, imm(rs)
  -> opcode = 29
  -> layout = opcode | rs | rs1 | imm = 48b
  -> offset is a 32b immediate
  => rd = imm[31:0]

- li.d rd, imm(rs)
  -> opcode = 30
  -> layout = opcode | rs | rs1 | imm = 80b
  -> offset is a 64b immediate
  => rd = imm[63:0]

- mov rd, rs
  -> opcode = 31
  -> layout = opcode | rd | rs = 16b
  => rd = rs
```

### Stack

```
- push rs
  -> opcode = 32
  -> layout = opcode | 0000 | rs = 16b
  => rsp = rsp - WORD_LEN/8 ; M[rsp] = rs
- pop rd
  -> opcode = 33
  -> layout = opcode | 0000 | rd = 16b
  => rd = rsp ; rsp = rsp + WORD_LEN/8
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
│         │ 1024 bytes that are un accessible, it helps to catch stack overflow
┊         ┊
┊ canary  ┊
┊         ┊
│   ---   │
├─────────┤
│         │ heap_base = stack_bottom + 1025
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
