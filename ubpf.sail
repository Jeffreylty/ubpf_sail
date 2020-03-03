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

val execute : ast -> unit effect {rreg, wreg}

/* ADDI instruction*/

union clause ast = ADDI : (regbits, bits(32))

function clause decode (regbits @ rt : regbits @ imm :32) =
  Some(ADDI(rt, imm))

function clause execute (ADDI(rt, imm)) =
{
    let rt1_val = X(rt) in
    let imm_ext : xlenbits = EXTS(imm) in
    let result = rt1_val + imm_ext in
    X(rt) = result
}

/* ADD_REG instruction */

union clause ast = ADD : (regbits, regbits)

function clause decode (regbits @ 0b000 @ rd : regbits @ 0b000 @ rs :regbits @ 0b00000 @ 0b100000) =
  Some(ADD(rd, rs))


function clause execute (ADD(rd, rs)) =
  {
    let opA = X(rs) in
    let opB = X(rd) in
    let result = opA + opB in
    X(rd) = result
  }
