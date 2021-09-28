(*<*)
theory Interval
  imports "HOL-Library.Product_Lexorder" Timestamp
begin
(*>*)

section \<open>Intervals\<close>

typedef (overloaded) ('a :: timestamp) \<I> = "{(i :: 'a, j :: 'a). 0 \<le> i \<and> i \<le> j}"
  by (intro exI[of _ "(0, 0)"]) auto

setup_lifting type_definition_\<I>

instantiation \<I> :: (timestamp) equal begin
lift_definition equal_\<I> :: "'a \<I> \<Rightarrow> 'a \<I> \<Rightarrow> bool" is "(=)" .
instance by standard (transfer, auto)
end

instantiation \<I> :: (timestamp) order begin
lift_definition less_eq_\<I> :: "'a \<I> \<Rightarrow> 'a \<I> \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_\<I> :: "'a \<I> \<Rightarrow> 'a \<I> \<Rightarrow> bool" is "(<)" .
instance
  by standard (transfer, auto simp add: dual_order.order_iff_strict Interval.less_eq_\<I>.rep_eq Rep_\<I>_inject)
end

lift_definition left :: "'a :: timestamp \<I> \<Rightarrow> 'a" is fst .
lift_definition right :: "'a :: timestamp \<I> \<Rightarrow> 'a" is snd .
definition mem :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> 'a \<I> \<Rightarrow> bool" where
  "mem i j I \<equiv> (i + left I \<le> j \<and> j \<le> i + right I)"

lemma mem_eq_enat:
  fixes i :: enat
  assumes "i \<le> j" "i \<noteq> \<infinity>"
  shows "mem i j I \<longleftrightarrow> (left I \<le> j - i \<and> (j - i) \<le> right I)"
  unfolding mem_def
  using assms
  by transfer (auto elim: less_eqE)

lemma mem_eq_ereal:
  fixes i :: ereal
  assumes "i \<le> j" "i \<noteq> - \<infinity>" "i \<noteq> \<infinity>"
  shows "mem i j I \<longleftrightarrow> (left I \<le> j - i \<and> (j - i) \<le> right I)"
  unfolding mem_def
  using assms
  by transfer (auto simp: add.commute ereal_le_minus_iff ereal_minus_le_iff)

lemma right_I_add_mono:
  fixes x :: "'a :: timestamp"
  shows "x \<le> x + right I"
  by transfer (auto intro: order_trans[OF _ add_mono, of _ _ 0])

lemma right_I_add_mono':
  fixes x :: "'a :: timestamp"
  shows "x \<le> right I + x"
  using right_I_add_mono
  by (subst add.commute) auto

definition interval :: "'a :: timestamp \<Rightarrow> 'a \<Rightarrow> 'a \<I>" where
  "interval l r = (if 0 \<le> l \<and> l \<le> r then Abs_\<I> (l, r) else undefined)"

lemma [code abstract]: "Rep_\<I> (interval l r) = (if 0 \<le> l \<and> l \<le> r then (l, r) else Rep_\<I> undefined)"
  unfolding interval_def using Abs_\<I>_inverse by auto

(*<*)
end
(*>*)
