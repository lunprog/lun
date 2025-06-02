# Virtual Machine Reference

The (new) Virtual Machine reference.

## Registers

General purpose registers (64 bits wide):
```
r0  r1  r2  r3
r4  r5  r6  r7
r8  r9  r10 r11
r12 r13 r14 r15
```

Special Registers:
```
rsp -> stack pointer
rip -> instruction pointer
rfl -> flags register
```

# Instructions

## Arithmetic & Logic

```
[ OPCODE | RD |TYPE|RS1 |RS2 | FUNCT1 ] -> 16 bits

where TYPE is a 4bit value as follows:
-  0: u8 arithmetics
-  1: u16 arithmetics
-  2: u32 arithmetics
-  3: u64 arithmetics
-  4: u128 arithmetics
-  5: i8 arithmetics
-  6: i16 arithmetics
-  7: i32 arithmetics
-  8: i64 arithmetics
-  9: i128 arithmetics
- 10: f16 arithmetics
- 11: f32 arithmetics
- 12: f64 arithmetics
- 13: f128 arithmetics
- 14: undefined
- 15: undefined

opcode = 0x00

- ADD:
  funct1 = 0
  rd = rs1 + rs2
- SUB:
  funct1 = 1
  rd = rs1 - rs2
- MUL:
  funct1 = 2
  rd = rs1 * rs2
- DIV:
  funct1 = 3
  rd = rs1 / rs2
- REM:
  funct1 = 4
  rd = rs1 % rs2
- CLT:
  funct1 = 5
  rd = rs1 < rs2
- CGE:
  funct1 = 6
  rd = rs1 >= rs2
- CEQ:
  funct1 = 7
  rd = rs1 == rs2
- CNE:
  funct1 = 8
  rd = rs1 != rs2
- AND:
  funct1 = 9
  rd = rs1 % rs2
- OR:
  funct1 = 10
  rd = rs1 % rs2
- XOR:
  funct1 = 11
  rd = rs1 % rs2
```

## Branching

```
TODO:
- jal rd, offset       => rd = pc + 4; pc += sext(offset)
- jalr rd, rs1, offset => t = pc + 4; pc = rs1 + offset ; rd = t
- beq rs1, rs2, offset => if rs1 == rs2 then pc += offset
- bne rs1, rs2, offset => if rs1 != rs2 then pc += offset
- blt rs1, rs2, offset => if rs1 < rs2 then pc += offset
- bge rs1, rs2, offset => if rs1 >= rs2 then pc += offset
```

## Memory

```
LOAD
- lb rd, offset => rd = mem(offset)[7:0]
- lh rd, offset => rd = mem(offset)[15:0]
- lw rd, offset => rd = mem(offset)[31:0]
- ld rd, offset => rd = mem(offset)[63:0]

STORE
- sb rs1, offset => mem(offset) = rs1[7:0]
- sh rs1, offset => mem(offset) = rs1[15:0]
- sw rs1, offset => mem(offset) = rs1[31:0]
- sd rs1, offset => mem(offset) = rs1[63:0]
```

## Moves

```
- mvi rd, imm[8, 16, 32, 64] => move immediate byte : rd = imm
  eg:
    mvi r1, 0x00 [8] -> here the immediate is just a byte
    mvi r1, 0xDEADBEEF [32] -> here the immediate is a word
- mov rd, rs  => move rs into rd: rd = rs
```

# Bus & Memory

Memory Map
```
┌─────────┐
│         │ 0
│ special │
│   ???   │ 255
├─────────┤
│         │ stack_top
┊         ┊
┊  stack  ┊
┊         ┊
│   RW-   │ stack_bottom = stack_top + stack_size
├─────────┤
│         │ program_start
┊         ┊
┊ program ┊
┊         ┊
│   R-X   │ program_end = program_start + program_size
├─────────┤
│         │ heap_base
┊         ┊
┊  heap   ┊
┊         ┊
│   ???   │
└─────────┘
```

`special`, `stack`, `program`, `heap` are memory regions, those are protected
through protections. Read, Write and eXecute are the protections, and each
region as it's protection represented as RWX (you can do everything) or ---
(you can do nothing), or ??? when the protection is more complicated than that.

`special` has `???` because every address has its own protection.

`heap` has `???` because the heap grows in regions and so every region has its
own protections, TODO: not sure about how exactly the heap would work though.

## Special

```
addr   prot   usage
-----------------
0      ---    null pointer
1      --X    call to foreign functions, defined by a library loaded by the VM
...    ---    the rest of the addresses
```

## Stack

The stack is a descending stack, it's bottom is defined as `stack_bottom`, the
stack cannot grow and the `stack_size` must be known before executing the
program.

## Program

The program size is the size of all the bytecode, it cannot grow, this region
is readonly and executable obviously.

## Heap

TODO: idk how it could work because we need to support freeing of memory, with
a garbage collector i think, but this heap thingy could not be the solution.

