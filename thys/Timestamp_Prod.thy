theory Timestamp_Prod
  imports Timestamp
begin

instantiation prod :: (bounded_semilattice_sup_bot, bounded_semilattice_sup_bot)
  bounded_semilattice_sup_bot
begin

definition bot_prod :: "'a \<times> 'b" where
  "bot_prod = (bot, bot)"

fun sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "sup (a, b) (c, d) = (sup a c, sup b d)"

fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod (a, b) (c, d) \<longleftrightarrow> a \<le> c \<and> b \<le> d"

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_prod x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  by standard (auto simp: add.commute bot_prod_def zero_prod_def less_prod_def)

end

instantiation prod :: (timestamp, timestamp) timestamp
begin

definition embed_nat_prod :: "nat \<Rightarrow> 'a \<times> 'b" where
  "embed_nat_prod n = (embed_nat n, embed_nat n)"

fun finite_ts_prod :: "'a \<times> 'b \<Rightarrow> bool" where
  "finite_ts_prod (x, y) = (finite_ts x \<and> finite_ts y)"

instance
  apply standard
  subgoal for i j
    using embed_nat_mono embed_nat_mono less_le
    by (fastforce simp: embed_nat_prod_def less_prod_def)
  apply (auto simp: embed_nat_prod_def intro: embed_nat_finite)[1]
  subgoal for x i
    apply (cases x)
    using embed_nat_unbounded
    by (auto simp: embed_nat_prod_def)
  subgoal for c d
    apply (cases c; cases d)
    using finite_ts_closed
    by auto+
  subgoal for c d a
    by (cases c; cases d; cases a) (auto simp add: add_mono_strict add_mono)
  done

end

instantiation prod :: (timestamp_strict, timestamp_strict) timestamp_strict
begin

instance
  apply standard
  subgoal for x
    by (cases x) (auto simp: all_finite_ts)
  subgoal for c d a
    apply (cases c; cases d; cases a)
    apply (auto simp add: add_mono less_prod_def order.strict_implies_order)
    apply (metis add_mono_strict antisym_conv2 order_refl)+
    done
  done

end

end
