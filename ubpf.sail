type xlen : Int = 64
type xlen_bytes : Int = 8
type xlenbits = bits(xlen)

/* Register of 64-vit in length */
register Xs : vector(64, dec, xlenbits)

type regbits = bits(4)

/* Define the getter and setter of register */
val rX : regbits -> xlenbits effect {rreg}

function rX(r) = 
  Xs[unsigned(r)];

val wX : (regbits, xlenbits) -> unit effect {wreg}

function wX(r, v) =
  Xs[unsigned(r)] = v;

overload X = {rX, wX}

scattered union ast

val decode : bits(64) -> option(ast) effect pure

val execute : ast -> unit effect {rreg, wreg}\\val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1) effect pure

function MAX(n) = pow2(n) - 1

/* EBPF_OP_ADD64_IMM instruction*/

union clause ast = ADDI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ rt : regbits @ 0b111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b1111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ rt : regbits @ 0b10111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b11111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b100111) = Some(MULI(rt,imm))

function clause execute (MULI(rt,imm)) =
  {
    let rt1_val = X(rt) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = rt1_val - imm_ext in
    X(rt) = result
  }

/* EBPF_OP_MUL64_REG instruction */

union clause ast = MUL : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ rs : regbits @ rd : regbits @ 0b101111) =
  Some(MUL(rd, rs))

function clause execute (MUL(rd,rs)) =
  {
    let opA = X(rs) in
    let opB = X(rd) in
    let result = opB * opA in
    X(rd) = result
  }


/* EBPF_OP_DIV64_IMM instruction */

union clause ast = DIVI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000  @ dst : regbits @ 0b110111) =
  Some(DIVI(dst, imm))

function clause execute (DIVI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = opA / imm_ext in
    X(dst) = result
  }

/* EBPF_OP_DIV64_REG instruction */

union clause ast = DIV : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits  @ dst : regbits @ 0b111111) =
  Some(DIV(dst, src))

function clause execute (DIV(dst,src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if (opB == 0) then 
      X(dst) = MAX(64)
    else
      let result = opA / opB in
      X(dst) = result
  }

/* EBPF_OP_OR64_IMM instruction */

union clause ast = ORI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b1000111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b1001111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b1010111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b1011111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b1100111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b1101111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b1110111) =
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

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b1111111) =
  Some(RSH(dst, src))

function clause execute (RSH(dst,src)) =
  {
    let opA = X(dst) in
    let opB = X(src) in
    let result = (opA >> opB) in
    X(dst) = result
  } 

/* EBPF_OP_NEG64 instruction */

union clause ast = NEG : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10000111) =
  Some(NEG(dst))

function clause execute (NEG(dst)) =
  {
    let opA = X(dst) in
    let result = ~(opA) +1 in
    X(dst) = result
  } 

/* EBPF_OP_MOD64_IMM instruction */

union clause ast = MODI : (regbits, bits(32))

function clause decode (imm : bits(32) @ 0b0000000000000000 @ 0b0000 @ dst : regbits @ 0b10010111) =
  Some(MODI(dst, imm))

function clause execute (MODI(dst,imm)) =
  {
    let opA = X(dst) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = (opA % imm_ext) in
    X(dst) = result
  } 

/* EBPF_OP_MOD64_REG instruction */

union clause ast = MOD : (regbits, regbits)

function clause decode (imm : bits(32) @ 0b0000000000000000 @ src : regbits @ dst : regbits @ 0b10011111) =
  Some(MOD(dst, src))

function clause execute (MOD(dst,src)) =
  {
    let opA = X(dst);
    let opB = X(src);
    if (opB == 0) then 
      X(dst) = MAX(64)
    else
      let result = ( opA % opB ) in
      X(dst) = result
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
















