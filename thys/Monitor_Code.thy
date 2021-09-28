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

definition mk_event :: "String.literal list \<Rightarrow> String.literal set" where "mk_event = set"

definition enat_interval :: "_ \<Rightarrow> _ \<Rightarrow> enat \<I>" where
  "enat_interval = interval"
definition sub_vydra :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, enat, 'e) vydra" where
  "sub_vydra = sub"
definition run_vydra :: " _ \<Rightarrow> _ \<Rightarrow> (String.literal, enat, 'e) vydra \<Rightarrow> _" where
  "run_vydra = run"
definition msize_fmla_vydra :: "(String.literal, enat) formula \<Rightarrow> nat" where
  "msize_fmla_vydra = msize_fmla"

export_code sub_vydra run_vydra msize_fmla_vydra
  Bool enat enat_interval nat_of_integer integer_of_nat mk_event
  in OCaml module_name VYDRA file_prefix "verified"

definition ereal_interval :: "_ \<Rightarrow> _ \<Rightarrow> ereal \<I>" where
  "ereal_interval = interval"
definition sub_real_vydra :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (String.literal, ereal, 'e) vydra" where
  "sub_real_vydra = sub"
definition run_real_vydra :: " _ \<Rightarrow> _ \<Rightarrow> (String.literal, ereal, 'e) vydra \<Rightarrow> _" where
  "run_real_vydra = run"
definition msize_fmla_real_vydra :: "(String.literal, ereal) formula \<Rightarrow> real" where
  "msize_fmla_real_vydra = msize_fmla"

end