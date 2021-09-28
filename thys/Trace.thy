(*<*)
theory Trace
  imports "HOL-Library.Stream" Timestamp
begin
(*>*)

section \<open>Infinite Traces\<close>

inductive sorted_list :: "'a :: order list \<Rightarrow> bool" where
  [intro]: "sorted_list []"
| [intro]: "sorted_list [x]"
| [intro]: "x \<le> y \<Longrightarrow> sorted_list (y # ys) \<Longrightarrow> sorted_list (x # y # ys)"

lemma sorted_list_app: "sorted_list xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<le> y) \<Longrightarrow> sorted_list (xs @ [y])"
  by (induction xs rule: sorted_list.induct) auto

lemma sorted_list_drop: "sorted_list xs \<Longrightarrow> sorted_list (drop n xs)"
  apply (induction xs arbitrary: n rule: sorted_list.induct)
    apply (auto)
  subgoal for x n
    by (cases n) auto
  subgoal for x y ys n
    by (cases n) auto
  done

lemma sorted_list_ConsD: "sorted_list (x # xs) \<Longrightarrow> sorted_list xs"
  by (auto elim: sorted_list.cases)

lemma sorted_list_atD: "sorted_list xs \<Longrightarrow> i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<le> xs ! j"
  apply (induction xs arbitrary: i j rule: sorted_list.induct)
    apply (auto)
  subgoal for x y ys i j
    apply (cases i)
     apply (auto)
    apply (induction j)
     apply auto
    apply (metis less_Suc_eq_0_disj nth_Cons_0 order.strict_iff_order order_trans)
    done
  done

coinductive ssorted :: "'a :: order stream \<Rightarrow> bool" where
  "shd s \<le> shd (stl s) \<Longrightarrow> ssorted (stl s) \<Longrightarrow> ssorted s"

lemma ssorted_siterate[simp]: "(\<And>n. n \<le> f n) \<Longrightarrow> ssorted (siterate f n)"
  by (coinduction arbitrary: n) auto

lemma ssortedD: "ssorted s \<Longrightarrow> s !! i \<le> stl s !! i"
  by (induct i arbitrary: s) (auto elim: ssorted.cases)

lemma ssorted_sdrop: "ssorted s \<Longrightarrow> ssorted (sdrop i s)"
  by (coinduction arbitrary: i s) (auto elim: ssorted.cases ssortedD)

lemma ssorted_monoD: "ssorted s \<Longrightarrow> i \<le> j \<Longrightarrow> s !! i \<le> s !! j"
proof (induct "j - i" arbitrary: j)
  case (Suc x)
  from Suc(1)[of "j - 1"] Suc(2-4) ssortedD[of s "j - 1"]
    show ?case by (cases j) (auto simp: le_Suc_eq Suc_diff_le)
qed simp

lemma sorted_stake: "ssorted s \<Longrightarrow> sorted_list (stake i s)"
  apply (induct i arbitrary: s)
   apply auto[1]
  subgoal for i s
    by (cases i) (auto elim: ssorted.cases)
  done

lemma ssorted_monoI: "\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j \<Longrightarrow> ssorted s"
  by (coinduction arbitrary: s)
    (auto dest: spec2[of _ "Suc _" "Suc _"] spec2[of _ 0 "Suc 0"])

lemma ssorted_iff_mono: "ssorted s \<longleftrightarrow> (\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j)"
  using ssorted_monoI ssorted_monoD by metis

typedef (overloaded) ('a, 'b :: timestamp) trace = "{s :: ('a set \<times> 'b) stream.
  ssorted (smap snd s) \<and> (\<forall>i. finite_ts (snd (s !! i))) \<and>
  (\<forall>i x. finite_ts x \<longrightarrow> (\<exists>j. \<not>snd (s !! j) \<le> snd (s !! i) + x))}"
  by (auto simp: embed_nat_mono embed_nat_finite embed_nat_unbounded
      intro!: exI[of _ "smap (\<lambda>n. ({}, embed_nat n)) nats"] ssorted_monoI)

setup_lifting type_definition_trace

lift_definition \<Gamma> :: "('a, 'b :: timestamp) trace \<Rightarrow> nat \<Rightarrow> 'a set" is
  "\<lambda>s i. fst (s !! i)" .
lift_definition \<tau> :: "('a, 'b :: timestamp) trace \<Rightarrow> nat \<Rightarrow> 'b" is
  "\<lambda>s i. snd (s !! i)" .

lemma \<tau>_mono[simp]: "i \<le> j \<Longrightarrow> \<tau> s i \<le> \<tau> s j"
  by transfer (auto simp: ssorted_iff_mono)

lemma ex_lt_\<tau>: "finite_ts x \<Longrightarrow> \<exists>j. \<not>\<tau> s j \<le> \<tau> s i + x"
  by transfer auto

lemma le_\<tau>_less: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j \<Longrightarrow> j < i \<Longrightarrow> \<tau> \<sigma> i = \<tau> \<sigma> j"
  by (simp add: antisym)

lemma less_\<tau>D: "\<tau> \<sigma> i < \<tau> \<sigma> j \<Longrightarrow> i < j"
  by (meson \<tau>_mono less_le_not_le not_le_imp_less)

abbreviation "\<Delta> s i \<equiv> \<tau> s i - \<tau> s (i - 1)"

lift_definition map_\<Gamma> :: "('a set \<Rightarrow> 'c set) \<Rightarrow> ('a, 'b :: timestamp) trace \<Rightarrow> ('c, 'b) trace" is
  "\<lambda>f s. smap (\<lambda>(x, i). (f x, i)) s"
  by (auto simp: stream.map_comp prod.case_eq_if cong: stream.map_cong)

lemma \<Gamma>_map_\<Gamma>[simp]: "\<Gamma> (map_\<Gamma> f s) i = f (\<Gamma> s i)"
  by transfer (simp add: prod.case_eq_if)

lemma \<tau>_map_\<Gamma>[simp]: "\<tau> (map_\<Gamma> f s) i = \<tau> s i"
  by transfer (simp add: prod.case_eq_if)

lemma map_\<Gamma>_id[simp]: "map_\<Gamma> id s = s"
  by transfer (simp add: stream.map_id)

lemma map_\<Gamma>_comp: "map_\<Gamma> g (map_\<Gamma> f s) = map_\<Gamma> (g \<circ> f) s"
  by transfer (simp add: stream.map_comp comp_def prod.case_eq_if case_prod_beta')

lemma map_\<Gamma>_cong: "\<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<Longrightarrow> (\<And>x. f\<^sub>1 x = f\<^sub>2 x) \<Longrightarrow> map_\<Gamma> f\<^sub>1 \<sigma>\<^sub>1 = map_\<Gamma> f\<^sub>2 \<sigma>\<^sub>2"
  by transfer (auto intro!: stream.map_cong)

section \<open>Finite Trace Prefixes\<close>

typedef (overloaded) ('a, 'b :: timestamp) prefix =
  "{p :: ('a set \<times> 'b) list. sorted_list (map snd p)}"
  by (auto intro!: exI[of _ "[]"])

setup_lifting type_definition_prefix

lift_definition last_ts :: "('a, 'b :: timestamp) prefix \<Rightarrow> 'b" is
  "\<lambda>p. (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p))" .

lift_definition first_ts :: "'b \<Rightarrow> ('a, 'b :: timestamp) prefix \<Rightarrow> 'b" is
  "\<lambda>n p. (case p of [] \<Rightarrow> n | _ \<Rightarrow> snd (hd p))" .

lift_definition pnil :: "('a, 'b :: timestamp) prefix" is "[]" by auto

lift_definition plen :: "('a, 'b :: timestamp) prefix \<Rightarrow> nat" is "length" .

lift_definition psnoc :: "('a, 'b :: timestamp) prefix \<Rightarrow> 'a set \<times> 'b \<Rightarrow> ('a, 'b) prefix" is
  "\<lambda>p x. if (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p)) \<le> snd x then p @ [x] else []"
proof (goal_cases sorted_psnoc)
  case (sorted_psnoc p x)
  then show ?case
    apply (induction p)
     apply (auto split: if_splits list.splits)
    subgoal for b p
      using sorted_list_ConsD[of _ "map snd p"]
      by (auto elim: sorted_list.cases split: if_splits list.splits)
    done
qed

instantiation prefix :: (type, timestamp) order begin

lift_definition less_eq_prefix :: "('a, 'b :: timestamp) prefix \<Rightarrow> ('a, 'b) prefix \<Rightarrow> bool" is
  "\<lambda>p q. \<exists>r. q = p @ r" .

definition less_prefix :: "('a, 'b :: timestamp) prefix \<Rightarrow> ('a, 'b) prefix \<Rightarrow> bool" where
  "less_prefix x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof (standard, goal_cases less refl trans antisym)
  case (less x y)
  then show ?case unfolding less_prefix_def ..
next
  case (refl x)
  then show ?case by transfer auto
next
  case (trans x y z)
  then show ?case by transfer auto
next
  case (antisym x y)
  then show ?case by transfer auto
qed

end

lemma psnoc_inject[simp]:
  "last_ts p \<le> snd x \<Longrightarrow> last_ts q \<le> snd y \<Longrightarrow> psnoc p x = psnoc q y \<longleftrightarrow> (p = q \<and> x = y)"
  by transfer auto

lift_definition prefix_of :: "('a, 'b :: timestamp) prefix \<Rightarrow> ('a, 'b) trace \<Rightarrow> bool" is
  "\<lambda>p s. stake (length p) s = p" .

lemma prefix_of_pnil[simp]: "prefix_of pnil \<sigma>"
  by transfer auto

lemma plen_pnil[simp]: "plen pnil = 0"
  by transfer auto

lemma plen_mono: "\<pi> \<le> \<pi>' \<Longrightarrow> plen \<pi> \<le> plen \<pi>'"
  by transfer auto

lemma prefix_of_psnocE: "prefix_of (psnoc p x) s \<Longrightarrow> last_ts p \<le> snd x \<Longrightarrow>
  (prefix_of p s \<Longrightarrow> \<Gamma> s (plen p) = fst x \<Longrightarrow> \<tau> s (plen p) = snd x \<Longrightarrow> P) \<Longrightarrow> P"
  by transfer (simp del: stake.simps add: stake_Suc)

lemma le_pnil[simp]: "pnil \<le> \<pi>"
  by transfer auto

lift_definition take_prefix :: "nat \<Rightarrow> ('a, 'b :: timestamp) trace \<Rightarrow> ('a, 'b) prefix" is stake
  by (auto dest: sorted_stake)

lemma plen_take_prefix[simp]: "plen (take_prefix i \<sigma>) = i"
  by transfer auto

lemma plen_psnoc[simp]: "last_ts \<pi> \<le> snd x \<Longrightarrow> plen (psnoc \<pi> x) = plen \<pi> + 1"
  by transfer auto

lemma prefix_of_take_prefix[simp]: "prefix_of (take_prefix i \<sigma>) \<sigma>"
  by transfer auto

lift_definition pdrop :: "nat \<Rightarrow> ('a, 'b :: timestamp) prefix \<Rightarrow> ('a, 'b) prefix" is drop
  by (auto simp: drop_map[symmetric] sorted_list_drop)

lemma pdrop_0[simp]: "pdrop 0 \<pi> = \<pi>"
  by transfer auto

lemma prefix_of_antimono: "\<pi> \<le> \<pi>' \<Longrightarrow> prefix_of \<pi>' s \<Longrightarrow> prefix_of \<pi> s"
  by transfer (auto simp del: stake_add simp add: stake_add[symmetric])

lemma \<tau>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<tau> s i = \<tau> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma \<Gamma>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<Gamma> s i = \<Gamma> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma ssorted_shift:
  "ssorted (xs @- s) = (sorted xs \<and> ssorted s \<and> (\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y))"
proof safe
  assume *: "ssorted (xs @- s)"
  then show "sorted xs"
    by (auto simp: ssorted_iff_mono shift_snth sorted_iff_nth_mono split: if_splits)
  from ssorted_sdrop[OF *, of "length xs"] show "ssorted s"
    by (auto simp: sdrop_shift)
  fix x y assume "x \<in> set xs" "y \<in> sset s"
  then obtain i j where "i < length xs" "xs ! i = x" "s !! j = y"
    by (auto simp: set_conv_nth sset_range)
  with ssorted_monoD[OF *, of i "j + length xs"] show "x \<le> y" by auto
next
  assume "sorted xs" "ssorted s" "\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y"
  then show "ssorted (xs @- s)"
  proof (coinduction arbitrary: xs s)
    case (ssorted xs s)
    with \<open>ssorted s\<close> show ?case
      by (subst (asm) ssorted.simps) (auto 0 4 simp: neq_Nil_conv shd_sset intro: exI[of _ "_ # _"])
  qed
qed

(*<*)
end
(*>*)
