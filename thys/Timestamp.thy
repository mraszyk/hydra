theory Timestamp
  imports "HOL-Library.Extended_Nat" "HOL-Library.Extended_Real"
begin

class timestamp = comm_monoid_add + bounded_semilattice_sup_bot +
  fixes embed_nat :: "nat \<Rightarrow> 'a" and finite_ts :: "'a \<Rightarrow> bool"
  assumes embed_nat_mono: "\<And>i j. i \<le> j \<Longrightarrow> embed_nat i \<le> embed_nat j"
    and embed_nat_finite: "\<And>i. finite_ts (embed_nat i)"
    and embed_nat_unbounded: "finite_ts x \<Longrightarrow> \<exists>j. \<not>embed_nat j \<le> embed_nat i + x"
    and finite_ts_closed: "finite_ts c \<Longrightarrow> finite_ts d \<Longrightarrow> finite_ts (c + d)"
    and add_mono: "c \<le> d \<Longrightarrow> a + c \<le> a + d"
begin

lemma add_mono_comm:
  fixes a :: 'a
  shows "c \<le> d \<Longrightarrow> c + a \<le> d + a"
  by (auto simp: add.commute add_mono)

end

instantiation prod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
begin

definition zero_prod :: "'a \<times> 'b" where
  "zero_prod = (zero_class.zero, zero_class.zero)"

fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "(a, b) + (c, d) = (a + c, b + d)"

instance
  by standard (auto simp: zero_prod_def ac_simps)

end

instantiation enat :: timestamp
begin

definition embed_nat_enat :: "nat \<Rightarrow> enat" where
  "embed_nat_enat n = n"

definition finite_ts_enat :: "enat \<Rightarrow> bool" where
  "finite_ts_enat n = (n \<noteq> \<infinity>)"

instance
  by standard (auto simp add: embed_nat_enat_def finite_ts_enat_def dest!: leD)

end

instantiation ereal :: timestamp
begin

definition embed_nat_ereal :: "nat \<Rightarrow> ereal" where
  "embed_nat_ereal n = ereal n"

definition finite_ts_ereal :: "ereal \<Rightarrow> bool" where
  "finite_ts_ereal n = (n \<noteq> \<infinity>)"

instance
  by standard (auto simp add: embed_nat_ereal_def finite_ts_ereal_def add.commute
     ereal_add_le_add_iff2 not_le less_PInf_Ex_of_nat ereal_less_ereal_Ex reals_Archimedean2)

end

class timestamp_strict = timestamp +
  assumes all_finite_ts: "finite_ts x"
    and add_mono_strict: "c < d \<Longrightarrow> a + c < a + d"
begin

lemma add_mono1: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
  by (metis add_commute add_mono_strict antisym_conv2 order.strict_implies_order eq_iff)

lemma add_mono2: "c \<le> d \<Longrightarrow> a + c \<le> a + d"
  by (metis add_mono_strict antisym_conv2 order.strict_implies_order eq_iff)

lemmas embed_nat_unbounded' = embed_nat_unbounded[OF all_finite_ts]

lemma embed_nat_strict_unbounded': "\<exists>j. \<not>embed_nat j \<le> x + embed_nat i"
  by (subst add.commute) (rule embed_nat_unbounded')

end

instantiation nat :: timestamp_strict
begin

definition embed_nat_nat :: "nat \<Rightarrow> nat" where
  "embed_nat_nat n = n"

definition finite_ts_nat :: "nat \<Rightarrow> bool" where
  "finite_ts_nat n = True"

instance
  by standard (auto simp add: embed_nat_nat_def finite_ts_nat_def dest!: leD)

end

typedef pos = "{x :: real. 0 \<le> x}"
  by auto

setup_lifting type_definition_pos

instantiation pos :: timestamp_strict
begin

lift_definition embed_nat_pos :: "nat \<Rightarrow> pos" is "\<lambda>n. real n"
  by auto

lift_definition finite_ts_pos :: "pos \<Rightarrow> bool" is "\<lambda>x. True" .

lift_definition bot_pos :: "pos" is "0"
  by auto

lift_definition zero_pos :: pos is "0"
  by auto

lift_definition plus_pos :: "pos \<Rightarrow> pos \<Rightarrow> pos" is "(+)"
  by auto

lift_definition sup_pos :: "pos \<Rightarrow> pos \<Rightarrow> pos" is max
  by auto

lift_definition less_eq_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" is "(<)" .

instance
  by (standard; transfer) (auto simp: not_le reals_Archimedean2)

end

end