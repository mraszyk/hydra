theory Timestamp_Lex
  imports Timestamp
begin

instantiation prod :: (bounded_semilattice_sup_bot, bounded_semilattice_sup_bot)
  bounded_semilattice_sup_bot
begin

definition bot_prod :: "'a \<times> 'b" where
  "bot_prod = (bot, bot)"

fun sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "sup_prod (a, b) (c, d) = (if a < c then (c, d) else if c < a then (a, b) else
    if a = c then (a, sup b d) else (sup a c, bot))"

fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod (a, b) (c, d) \<longleftrightarrow> a < c \<or> (a = c \<and> b \<le> d)"

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_prod x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  apply standard
         apply (auto simp: zero_prod_def less_prod_def)[2]
  subgoal for x y z
    using order.strict_trans
    by (cases x; cases y; cases z) auto
  subgoal for x y
    by (cases x; cases y) auto
  subgoal for x y
    by (cases x; cases y) (auto simp add: sup.commute sup.strict_order_iff)
  subgoal for x y
    by (cases x; cases y) (auto simp add: sup.commute sup.strict_order_iff)
  subgoal for y x z
    apply (cases x; cases y; cases z)
    apply (auto)
    apply (metis sup.strict_order_iff sup_assoc)
    done
  subgoal for a
    apply (cases a)
    apply (auto simp: bot_prod_def)
    using bot.not_eq_extremum by blast
  done

end

(*
instantiation prod :: (timestamp_strict, timestamp) timestamp
begin

definition embed_nat_prod :: "nat \<Rightarrow> 'a \<times> 'b" where
  "embed_nat_prod n = (embed_nat n, embed_nat n)"

definition finite_ts_prod :: "'a \<times> 'b \<Rightarrow> bool" where
  "finite_ts_prod xy = True"

instance
  apply standard
  subgoal for i j
    using embed_nat_mono embed_nat_mono less_le
    by (fastforce simp: embed_nat_prod_def less_prod_def)
     apply (auto simp: finite_ts_prod_def)[1]
  subgoal for x i
    apply (cases x)
    using embed_nat_unbounded'[of i] dual_order.order_iff_strict
    by (fastforce simp: embed_nat_prod_def)
   apply (auto simp: finite_ts_prod_def)[1]
  subgoal for c d a
    by (cases c; cases d; cases a) (auto simp add: add_mono_strict add_mono)
  done

end
*)

instantiation prod :: (timestamp_strict, timestamp_strict) timestamp_strict
begin

definition embed_nat_prod :: "nat \<Rightarrow> 'a \<times> 'b" where
  "embed_nat_prod n = (embed_nat n, embed_nat n)"

definition finite_ts_prod :: "'a \<times> 'b \<Rightarrow> bool" where
  "finite_ts_prod xy = True"

instance
  apply standard
  subgoal for i j
    using embed_nat_mono less_le
    apply (auto simp: embed_nat_prod_def less_prod_def)
    by (simp add: embed_nat_mono)
  apply (auto simp: finite_ts_prod_def)[1]
  subgoal for x i
    apply (cases x)
    apply (auto simp: embed_nat_prod_def)
    apply (metis dual_order.order_iff_strict embed_nat_unbounded')
    done
  apply (auto simp: finite_ts_prod_def)[1]
  subgoal for c d a
    by (cases c; cases d; cases a) (auto simp: add_mono add_mono_strict)
  apply (simp add: finite_ts_prod_def)
  subgoal for c d a
    apply (cases c; cases d; cases a)
    apply (auto simp add: add_mono_strict less_prod_def order.strict_implies_order)
      apply (metis add_mono_strict sup.strict_order_iff)
     apply (metis add_mono_strict sup.strict_order_iff)
    by (metis add_mono_strict dual_order.order_iff_strict less_le_not_le)
  done

end

end
