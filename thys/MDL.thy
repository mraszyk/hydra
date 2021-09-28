theory MDL
  imports Interval Trace
begin

section \<open>Formulas and Satisfiability\<close>

declare [[typedef_overloaded]]

datatype ('a, 'b :: timestamp) formula = Bool bool | Atom 'a | Neg "('a, 'b) formula" |
  Bin "bool \<Rightarrow> bool \<Rightarrow> bool" "('a, 'b) formula" "('a, 'b) formula" |
  Prev "'b \<I>" "('a, 'b) formula" | Next "'b \<I>" "('a, 'b) formula" |
  Since "('a, 'b) formula" "'b \<I>" "('a, 'b) formula" |
  Until "('a, 'b) formula" "'b \<I>" "('a, 'b) formula" |
  MatchP "'b \<I>" "('a, 'b) regex" | MatchF "'b \<I>" "('a, 'b) regex"
  and ('a, 'b) regex = Wild | Test "('a, 'b) formula" |
  Plus "('a, 'b) regex" "('a, 'b) regex" | Times "('a, 'b) regex" "('a, 'b) regex" |
  Star "('a, 'b) regex"

fun FR_fmla :: "('a, 'b :: timestamp) formula \<Rightarrow> 'b"
  and FR_regex :: "('a, 'b) regex \<Rightarrow> 'b" where
  "FR_fmla (Bool b) = 0"
| "FR_fmla (Atom a) = 0"
| "FR_fmla (Neg phi) = FR_fmla phi"
| "FR_fmla (Bin f phi psi) = sup (FR_fmla phi) (FR_fmla psi)"
| "FR_fmla (Prev I phi) = FR_fmla phi"
| "FR_fmla (Next I phi) = right I + FR_fmla phi"
| "FR_fmla (Since phi I psi) = sup (FR_fmla phi) (FR_fmla psi)"
| "FR_fmla (Until phi I psi) = right I + sup (FR_fmla phi) (FR_fmla psi)"
| "FR_fmla (MatchP I r) = FR_regex r"
| "FR_fmla (MatchF I r) = right I + FR_regex r"
| "FR_regex Wild = 0"
| "FR_regex (Test phi) = FR_fmla phi"
| "FR_regex (Plus r s) = sup (FR_regex r) (FR_regex s)"
| "FR_regex (Times r s) = sup (FR_regex r) (FR_regex s)"
| "FR_regex (Star r) = FR_regex r"

lemma FR_pos:
  fixes \<phi> :: "('a, 'b :: timestamp) formula"
    and r :: "('a, 'b) regex"
  shows "0 \<le> FR_fmla \<phi>" "0 \<le> FR_regex r"
  using right_I_add_mono' order.trans
   apply (induction rule: FR_fmla_FR_regex.induct)
                apply (auto simp add: sup.coboundedI2)
        apply fastforce
       apply fastforce
      apply fastforce
  apply (meson sup.cobounded1)
  using sup.coboundedI2 apply blast+
  done

fun bounded_future_fmla :: "('a, 'b :: timestamp) formula \<Rightarrow> bool"
  and bounded_future_regex :: "('a, 'b) regex \<Rightarrow> bool" where
  "bounded_future_fmla (Bool b) \<longleftrightarrow> True"
| "bounded_future_fmla (Atom a) \<longleftrightarrow> True"
| "bounded_future_fmla (Neg phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_fmla (Bin f phi psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi"
| "bounded_future_fmla (Prev I phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_fmla (Next I phi) \<longleftrightarrow> bounded_future_fmla phi \<and> finite_ts (right I)"
| "bounded_future_fmla (Since phi I psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi"
| "bounded_future_fmla (Until phi I psi) \<longleftrightarrow> bounded_future_fmla phi \<and> bounded_future_fmla psi \<and>
     finite_ts (right I)"
| "bounded_future_fmla (MatchP I r) \<longleftrightarrow> bounded_future_regex r"
| "bounded_future_fmla (MatchF I r) \<longleftrightarrow> bounded_future_regex r \<and> finite_ts (right I)"
| "bounded_future_regex Wild \<longleftrightarrow> True"
| "bounded_future_regex (Test phi) \<longleftrightarrow> bounded_future_fmla phi"
| "bounded_future_regex (Plus r s) \<longleftrightarrow> bounded_future_regex r \<and> bounded_future_regex s"
| "bounded_future_regex (Times r s) \<longleftrightarrow> bounded_future_regex r \<and> bounded_future_regex s"
| "bounded_future_regex (Star r) \<longleftrightarrow> bounded_future_regex r"

lemmas regex_induct[case_names Wild Test Plus Times Star, induct type: regex] =
  regex.induct[of "\<lambda>_. True", simplified]

definition "BTest b \<equiv> Test (Bool b)"
definition "BaseF \<phi> \<equiv> Times (Test \<phi>) Wild"
definition "BaseP \<phi> \<equiv> Times Wild (Test \<phi>)"
definition "PossiblyF r I \<phi> \<equiv> MatchF I (Times r (Test \<phi>))"
definition "PossiblyP \<phi> I r \<equiv> MatchP I (Times (Test \<phi>) r)"
definition "Once I \<phi> \<equiv> Since (Bool True) I \<phi>"
definition "Historically I \<phi> \<equiv> Neg (Once I (Neg \<phi>))"
definition "Eventually I \<phi> \<equiv> Until (Bool True) I \<phi>"
definition "Always I \<phi> \<equiv> Neg (Eventually I (Neg \<phi>))"

locale MDL =
  fixes \<sigma> :: "('a, 'b :: timestamp) trace"
begin

fun sat :: "nat \<Rightarrow> ('a, 'b) formula \<Rightarrow> bool"
  and match :: "('a, 'b) regex \<Rightarrow> (nat \<times> nat) set" where
  "sat i (Bool b) = b"
| "sat i (Atom a) = (a \<in> \<Gamma> \<sigma> i)"
| "sat i (Neg \<phi>) = (\<not> sat i \<phi>)"
| "sat i (Bin f \<phi> \<psi>) = (f (sat i \<phi>) (sat i \<psi>))"
| "sat i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> sat j \<phi>)"
| "sat i (Next I \<phi>) = (mem (\<tau> \<sigma> i) (\<tau> \<sigma> (Suc i)) I \<and> sat (Suc i) \<phi>)"
| "sat i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> sat j \<psi> \<and> (\<forall>k \<in> {j<..i}. sat k \<phi>))"
| "sat i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> sat j \<psi> \<and> (\<forall>k \<in> {i..<j}. sat k \<phi>))"
| "sat i (MatchP I r) = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> (j, i) \<in> match r)"
| "sat i (MatchF I r) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> (i, j) \<in> match r)"
| "match Wild = {(i, i + 1) | i. True}"
| "match (Test \<phi>) = {(i, i) | i. sat i \<phi>}"
| "match (Plus r s) = match r \<union> match s"
| "match (Times r s) = match r O match s"
| "match (Star r) = rtrancl (match r)"

lemma prev_rewrite: "sat i (Prev I \<phi>) \<longleftrightarrow> sat i (PossiblyP \<phi> I Wild)"
  apply (auto simp: PossiblyP_def split: nat.splits)
  subgoal for j
    apply (auto intro!: exI[of _ j])
    done
  done

lemma next_rewrite: "sat i (Next I \<phi>) \<longleftrightarrow> sat i (PossiblyF Wild I \<phi>)"
  by (fastforce simp: PossiblyF_def intro: exI[of _ "Suc i"])

lemma trancl_Base: "{(i, Suc i) |i. P i}\<^sup>* = {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}"
proof -
  have "(x, y) \<in> {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}"
    if "(x, y) \<in> {(i, Suc i) |i. P i}\<^sup>*" for x y
    using that by (induct rule: rtrancl_induct) (auto simp: less_Suc_eq)
  moreover have "(x, y) \<in> {(i, Suc i) |i. P i}\<^sup>*"
    if "(x, y) \<in> {(i, j). i \<le> j \<and> (\<forall>k\<in>{i..<j}. P k)}" for x y
    using that unfolding mem_Collect_eq prod.case Ball_def
    by (induct y arbitrary: x)
      (auto 0 3 simp: le_Suc_eq intro: rtrancl_into_rtrancl[rotated])
  ultimately show ?thesis by blast
qed

lemma Ball_atLeastLessThan_reindex:
  "(\<forall>k\<in>{j..<i}. P (Suc k)) = (\<forall>k \<in> {j<..i}. P k)"
  by (auto simp: less_eq_Suc_le less_eq_nat.simps split: nat.splits)

lemma since_rewrite: "sat i (Since \<phi> I \<psi>) \<longleftrightarrow> sat i (PossiblyP \<psi> I (Star (BaseP \<phi>)))"
proof (rule iffI)
  assume "sat i (Since \<phi> I \<psi>)"
  then obtain j where j_def: "j \<le> i" "mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I" "sat j \<psi> "
    "\<forall>k \<in> {j..<i}. sat (Suc k) \<phi>"
    by auto
  have match_BaseP: "match (BaseP \<phi>) = {(k, Suc k) | k. (k, Suc k) \<in> match (BaseP \<phi>)}"
    by (auto simp: BaseP_def)
  have "\<And>k. k \<in> {j..<i} \<Longrightarrow> (k, Suc k) \<in> match (BaseP \<phi>)"
    using j_def(4)
    by (auto simp: BaseP_def)
  then have "(j, i) \<in> (match (BaseP \<phi>))\<^sup>*"
    using j_def(1) trancl_Base
    by (subst match_BaseP) auto
  then show "sat i (PossiblyP \<psi> I (Star (BaseP \<phi>)))"
    using j_def(1,2,3)
    by (auto simp: PossiblyP_def)
next
  assume "sat i (PossiblyP \<psi> I (Star (BaseP \<phi>)))"
  then obtain j where j_def: "j \<le> i" "mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I" "(j, i) \<in> (match (BaseP \<phi>))\<^sup>*" "sat j \<psi>"
    by (auto simp: PossiblyP_def)
  have match_BaseP: "match (BaseP \<phi>) = {(k, Suc k) | k. (k, Suc k) \<in> match (BaseP \<phi>)}"
    by (auto simp: BaseP_def)
  have "\<And>k. k \<in> {j..<i} \<Longrightarrow> (k, Suc k) \<in> match (BaseP \<phi>)"
    using j_def(3) trancl_Base[of "\<lambda>k. (k, Suc k) \<in> match (BaseP \<phi>)"]
    by (auto simp: match_BaseP[symmetric])
  then have "\<forall>k \<in> {j..<i}. sat (Suc k) \<phi>"
    by (fastforce simp: BaseP_def)
  then show "sat i (Since \<phi> I \<psi>)"
    using j_def(1,2,4) Ball_atLeastLessThan_reindex[of j i "\<lambda>k. sat k \<phi>"]
    by (auto simp: BaseP_def intro: exI[of _ j])
qed

lemma until_rewrite: "sat i (Until \<phi> I \<psi>) \<longleftrightarrow> sat i (PossiblyF (Star (BaseF \<phi>)) I \<psi>)"
proof (rule iffI)
  assume "sat i (Until \<phi> I \<psi>)"
  then obtain j where j_def: "j \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I" "sat j \<psi> "
    "\<forall>k \<in> {i..<j}. sat k \<phi>"
    by auto
  have match_BaseF: "match (BaseF \<phi>) = {(k, Suc k) | k. (k, Suc k) \<in> match (BaseF \<phi>)}"
    by (auto simp: BaseF_def)
  have "\<And>k. k \<in> {i..<j} \<Longrightarrow> (k, Suc k) \<in> match (BaseF \<phi>)"
    using j_def(4)
    by (auto simp: BaseF_def)
  then have "(i, j) \<in> (match (BaseF \<phi>))\<^sup>*"
    using j_def(1) trancl_Base
    by (subst match_BaseF) auto
  then show "sat i (PossiblyF (Star (BaseF \<phi>)) I \<psi>)"
    using j_def(1,2,3)
    by (auto simp: PossiblyF_def)
next
  assume "sat i (PossiblyF (Star (BaseF \<phi>)) I \<psi>)"
  then obtain j where j_def: "j \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I" "(i, j) \<in> (match (BaseF \<phi>))\<^sup>*" "sat j \<psi>"
    by (auto simp: PossiblyF_def)
  have match_BaseF: "match (BaseF \<phi>) = {(k, Suc k) | k. (k, Suc k) \<in> match (BaseF \<phi>)}"
    by (auto simp: BaseF_def)
  have "\<And>k. k \<in> {i..<j} \<Longrightarrow> (k, Suc k) \<in> match (BaseF \<phi>)"
    using j_def(3) trancl_Base[of "\<lambda>k. (k, Suc k) \<in> match (BaseF \<phi>)"]
    by (auto simp: match_BaseF[symmetric])
  then have "\<forall>k \<in> {i..<j}. sat k \<phi>"
    by (fastforce simp: BaseF_def)
  then show "sat i (Until \<phi> I \<psi>)"
    using j_def(1,2,4)
    by auto
qed

lemma match_le: "(i, j) \<in> match r \<Longrightarrow> i \<le> j"
proof (induction r arbitrary: i j)
  case (Times r s)
  then show ?case using order.trans by fastforce
next
  case (Star r)
  from Star.prems show ?case
    unfolding match.simps
    by (induct i j rule: rtrancl.induct) (force dest: Star.IH)+
qed auto

lemma match_Times: "(i, i + n) \<in> match (Times r s) \<longleftrightarrow>
  (\<exists>k \<le> n. (i, i + k) \<in> match r \<and> (i + k, i + n) \<in> match s)"
  using match_le by auto (metis le_iff_add nat_add_left_cancel_le)

lemma rtrancl_unfold: "(x, z) \<in> rtrancl R \<Longrightarrow>
  x = z \<or> (\<exists>y. (x, y) \<in> R \<and> x \<noteq> y \<and> (y, z) \<in> rtrancl R)"
  by (induction x z rule: rtrancl.induct) auto

lemma match_Star: "(i, i + Suc n) \<in> match (Star r) \<longleftrightarrow>
  (\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and> (i + 1 + k, i + Suc n) \<in> match (Star r))"
proof (rule iffI)
  assume assms: "(i, i + Suc n) \<in> match (Star r)"
  obtain k where k_def: "(i, k) \<in> local.match r" "i \<le> k" "i \<noteq> k"
    "(k, i + Suc n) \<in> (local.match r)\<^sup>*"
    using rtrancl_unfold[OF assms[unfolded match.simps]] match_le by auto
  from k_def(4) have "(k, i + Suc n) \<in> match (Star r)"
    unfolding match.simps by simp
  then have k_le: "k \<le> i + Suc n"
    using match_le by blast
  from k_def(2,3) obtain k' where k'_def: "k = i + Suc k'"
    by (metis Suc_diff_Suc le_add_diff_inverse le_neq_implies_less)
  show "\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and> (i + 1 + k, i + Suc n) \<in> match (Star r)"
    using k_def k_le unfolding k'_def by auto
next
  assume assms: "\<exists>k \<le> n. (i, i + 1 + k) \<in> match r \<and>
    (i + 1 + k, i + Suc n) \<in> match (Star r)"
  then show "(i, i + Suc n) \<in> match (Star r)"
    by (induction n) auto
qed

end

end
