overload operator == = {eq_anything}
overload ~ = {not_bool, not_vec}
overload not = {not_bool}
overload operator != = {neq_anything}
val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec b = match b {
  bitzero => 0b0,
  _ => 0b1
}

overload operator ^ = {xor_vec, int_power, concat_str}
overload operator + = {add_range, add_int, add_vec, add_vec_int}
overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int}
overload operator * = {mult_int}
overload operator / = {ediv_int, div}
overload operator % = {emod_int, mod}
