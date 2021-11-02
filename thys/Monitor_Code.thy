theory Monitor_Code
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" Monitor
begin

code_printing
  code_module "IArray" \<rightharpoonup> (OCaml)
\<open>module IArray : sig
  val length' : 'a array -> Z.t
  val sub' : 'a array * Z.t -> 'a
end = struct

let length' xs = Z.of_int (Array.length xs);;

let sub' (xs, i) = Array.get xs (Z.to_int i);;

end\<close> for type_constructor iarray constant IArray.length' IArray.sub'

code_reserved OCaml IArray

code_printing
  type_constructor iarray \<rightharpoonup> (OCaml) "_ array"
| constant iarray_of_list \<rightharpoonup> (OCaml) "Array.of'_list"
| constant IArray.list_of \<rightharpoonup> (OCaml) "Array.to'_list"
| constant IArray.length' \<rightharpoonup> (OCaml) "IArray.length'"
| constant IArray.sub' \<rightharpoonup> (OCaml) "IArray.sub'"

lemma iarray_list_of_inj: "IArray.list_of xs = IArray.list_of ys \<Longrightarrow> xs = ys"
  by (cases xs; cases ys) auto

instantiation iarray :: (ccompare) ccompare
begin

definition ccompare_iarray :: "('a iarray \<Rightarrow> 'a iarray \<Rightarrow> order) option" where
  "ccompare_iarray = (case ID CCOMPARE('a list) of None \<Rightarrow> None
  | Some c \<Rightarrow> Some (\<lambda>xs ys. c (IArray.list_of xs) (IArray.list_of ys)))"

instance
  apply standard
  apply unfold_locales
  using comparator.sym[OF ID_ccompare'] comparator.weak_eq[OF ID_ccompare']
    comparator.trans[OF ID_ccompare'] iarray_list_of_inj
    apply (fastforce simp: ccompare_iarray_def split: option.splits)+
  done

end

derive (rbt) mapping_impl iarray

definition mk_db :: "String.literal list \<Rightarrow> String.literal set" where "mk_db = set"

definition interval_enat :: "_ \<Rightarrow> _ \<Rightarrow> enat \<I>" where
  "interval_enat = interval"
definition init_vydra_string_enat :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, enat, 'e) vydra" where
  "init_vydra_string_enat = init_vydra"
definition run_vydra_string_enat :: " _  \<Rightarrow> (String.literal, enat, 'e) vydra \<Rightarrow> _" where
  "run_vydra_string_enat = run_vydra"

definition interval_ereal :: "_ \<Rightarrow> _ \<Rightarrow> ereal \<I>" where
  "interval_ereal = interval"
definition init_vydra_string_ereal :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, ereal, 'e) vydra" where
  "init_vydra_string_ereal = init_vydra"
definition run_vydra_string_ereal :: " _  \<Rightarrow> (String.literal, ereal, 'e) vydra \<Rightarrow> _" where
  "run_vydra_string_ereal = run_vydra"

export_code init_vydra_string_enat run_vydra_string_enat
  Bool enat interval_enat nat_of_integer integer_of_nat mk_db
  in OCaml module_name VYDRA file_prefix "verified"

end