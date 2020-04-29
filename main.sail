register InstCount : int
val fetch_and_execute : unit -> bool effect {barr, eamem, escape, rmem, rreg, wmv, wreg, undef, wmvt, rmemt}
function fetch_and_execute () = {
  PC = NextPC;
  NextPC = PC + 8;
  loop_again : bool = true;
    let pc_pa = TranslatePC(PC);
    InstCount = InstCount + 1;
    /*print_bits("pa: ", pc_pa);*/
    LastInstrBits = CurrentInstrBits;
    let instr_next = MEMr_wrapper(pc_pa, 4);
    let instr_ast = decode(instr_next);
    match instr_ast {
      Some(EXIT()) => {
                     print("simulation stopped due to halt instruction.");
                     loop_again = false
                   },
      Some(ast) => {

                execute(ast)
      },
      None()    => { print("Decode failed"); loop_again=false } /* Never expect this -- unknown instruction should actually result in reserved instruction ISA-level exception (see mips_ri.sail). */
    }
  loop_again;
}

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  lem: "elf_entry",
  c: "elf_entry"
} : unit -> int

val init_registers : bits(64) -> unit effect {wreg, escape}

function init_registers (initialPC) = {
//   init_cp0_state();
//   init_cp2_state();
  NextPC = initialPC;
}

val main : unit -> unit effect {barr, eamem, escape, rmem, rreg, undef, wmv, wreg, rmemt, wmvt}

function main () = {
  init_registers(to_bits(64, elf_entry()));
  while (fetch_and_execute()) do {
    /* uncomment to print IPS every 10M instructions (~10s) 
    intervalCount = intervalCount + 1;
    if (intervalCount == 10000000) then {
      endTime = get_time_ns();
      elapsed = endTime - intervalStart;
      inst_1e9 = intervalCount * 1000000000;
      ips = inst_1e9 / elapsed;
      print_int("*IPS*: ", ips);
      intervalStart = get_time_ns();
      intervalCount = 0;
    };
    */
    ();
  };
  print_int("Executed instructions: ", InstCount);
}
