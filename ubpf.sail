$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
$include <option.sail>
$include <vector_dec.sail>
$include <string.sail>


default Order dec

type xlen : Int = 64
type xlen_bytes : Int = 8
type xlenbits = bits(xlen)

register PC : xlenbits
register nextPC : xlenbits

infix 4 <_u
infix 4 >_u
infix 4 >=_u
infix 4 <=_u
infix 4 <_s
infix 4 >=_s
infix 4 >_s
infix 4 <=_s


val operator <_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool

function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >_u  (x, y) = unsigned(x) > unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator >_s  (x, y) = signed(x) > signed(y)
function operator <=_s (x, y) = signed(x) <= signed(y)


infix 7 >>
infix 7 <<

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)
val "shift_bits_left"  : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

val "shiftl" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)
val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

overload operator >> = {shift_bits_right, shiftr}
overload operator << = {shift_bits_left, shiftl}

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool

val cast bit_to_bool : bit -> bool
function bit_to_bool b = match b {
  bitone => true,
  _ => false
}

val cast bits_to_bool : bits(1) -> bool
function bits_to_bool x = bit_to_bool(x[0])

overload operator == = {eq_string, eq_anything}

val not_bit : bit -> bit

function not_bit(b) = if b == bitone then bitzero else bitone

overload ~ = {not_bool, not_vec, not_bit}

val sub_range = {ocaml: "sub_int", lem: "integerMinus", coq: "sub_range"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val sub_vec = {c : "sub_bits", _:"sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {c:"sub_bits_int", _: "sub_vec_int"} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int}

val xor_vec = {c: "xor_bits" , _: "xor_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)
overload operator ^ = {xor_vec, int_power, concat_str}
overload operator / = {ediv_int, div}
overload operator % = {emod_int, mod}

overload operator & = {and_vec}

infix 7 *_u
val operator *_u = "mult_vec" : forall 'n . (bits('n), bits('n)) -> bits(2 * 'n)


val "add_int" : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val  "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)
overload operator + = {add_range, add_int, add_vec, add_vec_int}

/* 11 Register of 64-bit in length */
register Xs : vector(16, dec, xlenbits)

type regbits = bits(4)

/* Define the getter and setter of register */
val rX : regbits -> xlenbits effect {rreg}

function rX(r) = 
  Xs[unsigned(r)]

val wX : (regbits, xlenbits) -> unit effect {wreg}

function wX(r, v) =
  Xs[unsigned(r)] = v

overload X = {rX, wX}

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

scattered union ast

val decode : bits(64) -> option(ast) effect pure

val execute : ast -> unit effect {rreg, wreg,rmem}
val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1) effect pure

/*!
THIS(n) returns 2 raised to the power _n_.
 */
val pow2 = "pow2" : forall 'n , 'n >= 0 . atom('n) -> atom(2 ^ 'n)

function MAX(n) = pow2(n) - 1

/* EBPF_OP_ADD64_IMM instruction*/

union clause ast = ADDI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ rt : regbits @ 0b00000111) =
  Some(ADDI(rt, imm))

function clause execute (ADDI(rt, imm)) =
{
    let rt1_val = X(rt) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = rt1_val + imm_ext in
    X(rt) = result
}

/* EBPF_OP_ADD64_REG instruction */

union clause ast = ADD : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b00001111) =
  Some(ADD(rd, rs))


function clause execute (ADD(rd, rs)) =
  {
    let opA = X(rs) in
    let opB = X(rd) in
    let result = opA + opB in
    X(rd) = result
  }

/* EBPF_OP_SUB64_IMM instruction */

union clause ast = SUBI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ rt : regbits @ 0b00010111) =
  Some(SUBI(rt, imm))

function clause execute (SUBI(rt, imm)) =
{
    let rt1_val = X(rt) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = rt1_val - imm_ext in
    X(rt) = result
}


/* EBPF_OP_SUB64_REG instruction */

union clause ast = SUB : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b00011111) =
  Some(SUB(rd, rs))


function clause execute (SUB(rd, rs)) =
  {
    let opA = X(rs) in
    let opB = X(rd) in
    let result = opB - opA in
    X(rd) = result
  }

  /* EBPF_OP_MUL64_IMM instruction */

union clause ast = MULI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b00100111) = Some(MULI(rd,imm))

function clause execute (MULI(rt,imm)) =
  {
    let rt1_val = X(rt) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = rt1_val *_u imm_ext in
    X(rt) = result[63..0]
  }

/* EBPF_OP_MUL64_REG instruction */

union clause ast = MUL : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b00101111) =
  Some(MUL(rd, rs))

function clause execute (MUL(rd,rs)) =
  {
    let opA = X(rs) in
    let opB = X(rd) in
    let result = opB *_u opA in
    X(rd) = result[63..0]
  }


/* EBPF_OP_DIV64_IMM instruction */
val quot_round_zero = {ocaml: "quot_round_zero", lem: "hardware_quot", coq: "Z.quot", _ : "tdiv_int"} : (int, int) -> int

val to_bits : forall 'l, 'l >= 0 .(atom('l), int) -> bits('l)
function to_bits (l, n) = get_slice_int(l, n, 0)


union clause ast = DIVI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000  @ dst : regbits @ 0b00110111) =
  Some(DIVI(dst, imm))

function clause execute (DIVI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let A = unsigned(opA[63..0]) in
    let B = unsigned(imm_ext[63..0]) in
    let result = quot_round_zero(A, B) in
    X(dst) = to_bits(64,result)
  }

/* EBPF_OP_DIV64_REG instruction */

union clause ast = DIV : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits  @ dst : regbits @ 0b00111111) =
  Some(DIV(dst, src))

function clause execute (DIV(dst,src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if (unsigned(opB) == 0) then 
      let result = MAX(64) in
      X(dst) = to_bits(64,result)
    else
      let A = unsigned(opA[63..0]) in
      let B = unsigned(opB[63..0]) in
      let result = quot_round_zero(A, B) in
      X(dst) = to_bits(64,result)
  }

/* EBPF_OP_OR64_IMM instruction */

union clause ast = ORI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b01000111) =
  Some(ORI(dst, imm))

function clause execute (ORI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA | imm_ext) in
    X(dst) = result
  }  

/* EBPF_OP_OR64_REG instruction */

union clause ast = OR : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b01001111) =
  Some(OR(dst, src))

function clause execute (OR(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = (opA | opB) in
    X(dst) = result
  }  


/* EBPF_OP_AND64_IMM instruction */

union clause ast = ANDI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b01010111) =
  Some(ANDI(dst, imm))

function clause execute (ANDI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA & imm_ext) in
    X(dst) = result
  } 

/* EBPF_OP_AND64_REG instruction */

union clause ast = AND : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b01011111) =
  Some(AND(dst, src))

function clause execute (AND(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = (opA & opB) in
    X(dst) = result
  }  

/* EBPF_OP_LSH64_IMM instruction */

union clause ast = LSHI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b01100111) =
  Some(LSHI(dst, imm))

function clause execute (LSHI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA << imm_ext) in
    X(dst) = result
  } 

/* EBPF_OP_LSH64_REG instruction */

union clause ast = LSH : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b01101111) =
  Some(LSH(dst, src))

function clause execute (LSH(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = (opA << opB) in
    X(dst) = result
  } 


/* EBPF_OP_RSH64_IMM instruction */

union clause ast = RSHI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b01110111) =
  Some(RSHI(dst, imm))

function clause execute (RSHI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA >> imm_ext) in
    X(dst) = result
  } 

/* EBPF_OP_RSH64_REG instruction */

union clause ast = RSH : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b01111111) =
  Some(RSH(dst, src))

function clause execute (RSH(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = (opA >> opB) in
    X(dst) = result
  } 

/* EBPF_OP_NEG64 instruction */

union clause ast = NEG : (regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10000111) =
  Some(NEG(dst))

function clause execute (NEG(dst)) =
  {
    let opA = X(dst) in
    let result = ~(opA) +1 in
    X(dst) = result
  } 

/* EBPF_OP_MOD64_IMM instruction */
val rem_round_zero = {ocaml: "rem_round_zero", lem: "hardware_mod", coq: "Z.rem", _ : "tmod_int"} : (int, int) -> int

union clause ast = MODI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10010111) =
  Some(MODI(dst, imm))

function clause execute (MODI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let A = unsigned(opA[63..0]) in
    let B = unsigned(imm_ext[63..0]) in
    let result = rem_round_zero(A,B) in
    X(dst) = to_bits(64,result)
  } 

/* EBPF_OP_MOD64_REG instruction */

union clause ast = MOD : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b10011111) =
  Some(MOD(dst, src))

function clause execute (MOD(dst,src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if (unsigned(opB) == 0) then 
      let result = MAX(64) in
      X(dst) = to_bits(64,result)
    else
      let A = unsigned(opA[63..0]) in
    let B = unsigned(opB[63..0]) in
    let result = rem_round_zero(A,B) in
    X(dst) = to_bits(64,result)
  } 


/* EBPF_OP_XOR64_IMM instruction */

union clause ast = XORI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10100111) =
  Some(XORI(dst, imm))

function clause execute (XORI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA ^ imm_ext) in
    X(dst) = result
  } 

/* EBPF_OP_XOR64_REG instruction */

union clause ast = XOR : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b10101111) =
  Some(XOR(dst, src))

function clause execute (XOR(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = ( opA ^ opB ) in
    X(dst) = result
  } 



/* EBPF_OP_MOV64_IMM instruction */

union clause ast = MOVI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10110111) =
  Some(MOVI(dst, imm))

function clause execute (MOVI(dst,imm)) =
  {
    let imm_ext : xlenbits = EXTS(imm) in
    X(dst) = imm_ext
  } 

/* EBPF_OP_MOV64_REG instruction */

union clause ast = MOV : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b10111111) =
  Some(MOV(dst, src))

function clause execute (MOV(dst,src)) =
  {
    let opB = X(src) in
    X(dst) = opB
  } 

/* EBPF_OP_ARSH64_IMM instruction */

union clause ast = ARSHI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b11000111) =
  Some(ARSHI(dst, imm))

function clause execute (ARSHI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let v128 : bits(128) = EXTS(opA) in
    let result = (v128 >> imm_ext)[63..0] in
    X(dst) = result
  } 

/* EBPF_OP_ARSH64_REG instruction */

union clause ast = ARSH : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(ARSH(dst, src))

function clause execute (ARSH(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let v128 : bits(128) = EXTS(opA) in
    let result = (v128 >> opB)[63..0] in
    X(dst) = result
  } 

/* EBPF_OP_JA */

union clause ast = JA : bits(16)

function clause decode (imm : bits(32) @ offset : bits(16) @ 0b0000 @ 0b0000 @ 0b11001111) =
  Some(JA(offset))

function clause execute (JA(offset)) =
  {
    PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JEQ_IMM */
union clause ast = JEQIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JEQIMM(dst, imm, offset))

function clause execute (JEQIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA == imm_ext then 
      PC = PC + EXTS(offset);
  } 


/* EBPF_OP_JEQ_REG */
union clause ast = JEQ : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JEQ(dst, offset, src))

function clause execute (JEQ(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA == opB then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JGT_IMM */
union clause ast = JGTIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JGTIMM(dst, imm, offset))

function clause execute (JGTIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA >_u imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JGT_REG */
union clause ast = JGT : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JGT(dst, offset, src))

function clause execute (JGT(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA  >_u opB then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JGE_IMM */
union clause ast = JGEIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JGEIMM(dst, imm, offset))

function clause execute (JGEIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA >=_u imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JGE_REG */
union clause ast = JGE : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JGE(dst, offset, src))

function clause execute (JGE(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA  >=_u opB then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JLT_IMM */
union clause ast = JLTIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JLTIMM(dst, imm, offset))

function clause execute (JLTIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA <_u imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JLT_REG */
union clause ast = JLT : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JLT(dst, offset, src))

function clause execute (JLT(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA  <_u opB then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JLE_IMM */
union clause ast = JLEIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JLEIMM(dst, imm, offset))

function clause execute (JLEIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA <=_u imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JLE_REG */
union clause ast = JLE : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JLE(dst, offset, src))

function clause execute (JLE(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA  <=_u opB then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSET_IMM */
union clause ast = JSETIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSETIMM(dst, imm, offset))

function clause execute (JSETIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    let result = (opA & imm_ext);
    if unsigned(opA & imm_ext) != 0 then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSET_REG */
union clause ast = JSET : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSET(dst, offset, src))

function clause execute (JSET(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if unsigned(opA & opB) != 0 then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_JNE_IMM */
union clause ast = JNEIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JNEIMM(dst, imm, offset))

function clause execute (JNEIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA != imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JNE_REG */
union clause ast = JNE : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JNE(dst, offset, src))

function clause execute (JNE(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA  != opB then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_JSGT_IMM */
union clause ast = JSGTIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSGTIMM(dst, imm, offset))

function clause execute (JSGTIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA >_s imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSGT_REG */
union clause ast = JSGT : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSGT(dst, offset, src))

function clause execute (JSGT(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA >_s opB then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_JSGE_IMM */
union clause ast = JSGEIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSGEIMM(dst, imm, offset))

function clause execute (JSGEIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA >=_s imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSGE_REG */
union clause ast = JSGE : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSGE(dst, offset, src))

function clause execute (JSGE(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA >=_s opB then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_JSLT_IMM */
union clause ast = JSLTIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSLTIMM(dst, imm, offset))

function clause execute (JSLTIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA <_s imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSLT_REG */
union clause ast = JSLT : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSLT(dst, offset, src))

function clause execute (JSLT(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA <_s opB then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_JSLE_IMM */
union clause ast = JSLEIMM : (regbits, bits(32), bits(16))

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSLEIMM(dst, imm, offset))

function clause execute (JSLEIMM(dst, imm, offset)) =
  {
    let opA = X(dst);
    let imm_ext : xlenbits = EXTS(imm);
    if opA <=_s imm_ext then 
      PC = PC + EXTS(offset);
  } 

/* EBPF_OP_JSLE_REG */
union clause ast = JSLE : (regbits, bits(16), regbits)

function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
  Some(JSLE(dst, offset, src))

function clause execute (JSLE(dst, offset, src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if opA <=_s opB then 
      PC = PC + EXTS(offset);
  } 

  /* EBPF_OP_EXIT */
// union clause ast = EXIT : (regbits, bits(16), regbits)

// function clause decode (imm : bits(32) @ offset : bits(16) @ src : regbits @ dst : regbits @ 0b11001111) =
//   Some(EXIT(dst, offset, src))

// function clause execute (EXIT(dst, offset, src)) =
//   {
//     let opA = X(dst);
//     let opB = X(src);
//     if opA <=_s opB then 
//       PC = PC + EXTS(offset);
//   } 

