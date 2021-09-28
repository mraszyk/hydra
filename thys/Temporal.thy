theory Temporal
  imports MDL NFA Window
begin

fun state_cnt :: "('a, 'b :: timestamp) regex \<Rightarrow> nat" where
  "state_cnt Wild = 1"
| "state_cnt (Test _) = 1"
| "state_cnt (Plus r s) = 1 + state_cnt r + state_cnt s"
| "state_cnt (Times r s) = state_cnt r + state_cnt s"
| "state_cnt (Star r) = 1 + state_cnt r"

lemma state_cnt_pos: "state_cnt r > 0"
  by (induction r rule: state_cnt.induct) auto

fun collect_subfmlas :: "('a, 'b :: timestamp) regex \<Rightarrow> ('a, 'b) formula list \<Rightarrow>
  ('a, 'b) formula list" where
  "collect_subfmlas Wild phis = phis"
| "collect_subfmlas (Test \<phi>) phis = (if \<phi> \<in> set phis then phis else phis @ [\<phi>])"
| "collect_subfmlas (Plus r s) phis = collect_subfmlas s (collect_subfmlas r phis)"
| "collect_subfmlas (Times r s) phis = collect_subfmlas s (collect_subfmlas r phis)"
| "collect_subfmlas (Star r) phis = collect_subfmlas r phis"

lemma bf_collect_subfmlas: "bounded_future_regex r \<Longrightarrow> phi \<in> set (collect_subfmlas r phis) \<Longrightarrow>
  phi \<in> set phis \<or> bounded_future_fmla phi"
  by (induction r phis rule: collect_subfmlas.induct) (auto split: if_splits)

lemma FR_collect_subfmlas: "phi \<in> set (collect_subfmlas r phis) \<Longrightarrow>
  phi \<in> set phis \<or> FR_fmla phi \<le> FR_regex r"
  by (induction r phis rule: collect_subfmlas.induct)
    (auto simp add: le_supI1 le_supI2 split: if_splits)

lemma collect_subfmlas_set: "set (collect_subfmlas r phis) = set (collect_subfmlas r []) \<union> set phis"
proof (induction r arbitrary: phis)
  case (Plus r1 r2)
  show ?case
    using Plus(1)[of phis] Plus(2)[of "collect_subfmlas r1 phis"]
      Plus(2)[of "collect_subfmlas r1 []"]
    by auto
next
  case (Times r1 r2)
  show ?case
    using Times(1)[of phis] Times(2)[of "collect_subfmlas r1 phis"]
      Times(2)[of "collect_subfmlas r1 []"]
    by auto
next
  case (Star r)
  show ?case
    using Star[of phis]
    by auto
qed auto

lemma collect_subfmlas_size: "x \<in> set (collect_subfmlas r []) \<Longrightarrow> size x < size r"
proof (induction r)
  case Wild
  then show ?case
    by auto
next
  case (Test phi)
  then show ?case
    by (auto split: if_splits)
next
  case (Plus r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Times r1 r2)
  then show ?case
    by (auto simp: collect_subfmlas_set[of r2 "collect_subfmlas r1 []"])
next
  case (Star r)
  then show ?case
    by fastforce
qed

lemma collect_subfmlas_app: "\<exists>phis'. collect_subfmlas r phis = phis @ phis'"
  by (induction r phis rule: collect_subfmlas.induct) auto

lemma length_collect_subfmlas: "length (collect_subfmlas r phis) \<ge> length phis"
  by (induction r phis rule: collect_subfmlas.induct) auto

fun pos :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "pos a [] = None"
| "pos a (x # xs) =
    (if a = x then Some 0 else (case pos a xs of Some n \<Rightarrow> Some (Suc n) | _ \<Rightarrow> None))"

lemma pos_sound: "pos a xs = Some i \<Longrightarrow> i < length xs \<and> xs ! i = a"
  by (induction a xs arbitrary: i rule: pos.induct) (auto split: if_splits option.splits)

lemma pos_complete: "pos a xs = None \<Longrightarrow> a \<notin> set xs"
  by (induction a xs rule: pos.induct) (auto split: if_splits option.splits)

fun build_nfa_impl :: "('a, 'b :: timestamp) regex \<Rightarrow> (state \<times> state \<times> ('a, 'b) formula list) \<Rightarrow>
  transition list" where
  "build_nfa_impl Wild (q0, qf, phis) = [wild_trans qf]"
| "build_nfa_impl (Test \<phi>) (q0, qf, phis) = (case pos \<phi> phis of
    Some n \<Rightarrow> [cond_eps qf n]
  | None \<Rightarrow> [cond_eps qf (length phis)])"
| "build_nfa_impl (Plus r s) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0 + 1, qf, phis);
        ts_s = build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis) in
    split_trans (q0 + 1) (q0 + 1 + state_cnt r) # ts_r @ ts_s)"
| "build_nfa_impl (Times r s) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0, q0 + state_cnt r, phis);
        ts_s = build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis) in
    ts_r @ ts_s)"
| "build_nfa_impl (Star r) (q0, qf, phis) = (
    let ts_r = build_nfa_impl r (q0 + 1, q0, phis) in
    split_trans (q0 + 1) qf # ts_r)"

lemma build_nfa_impl_state_cnt: "length (build_nfa_impl r (q0, qf, phis)) = state_cnt r"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis rule: build_nfa_impl.induct)
    (auto split: option.splits)

lemma build_nfa_impl_not_Nil: "build_nfa_impl r (q0, qf, phis) \<noteq> []"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis rule: build_nfa_impl.induct)
    (auto split: option.splits)

lemma build_nfa_impl_state_set: "t \<in> set (build_nfa_impl r (q0, qf, phis)) \<Longrightarrow>
  state_set t \<subseteq> {q0..<q0 + length (build_nfa_impl r (q0, qf, phis))} \<union> {qf}"
  by (induction r "(q0, qf, phis)" arbitrary: q0 qf phis t rule: build_nfa_impl.induct)
    (fastforce simp add: build_nfa_impl_state_cnt state_cnt_pos build_nfa_impl_not_Nil
      split: option.splits)+

lemma build_nfa_impl_fmla_set: "t \<in> set (build_nfa_impl r (q0, qf, phis)) \<Longrightarrow>
  n \<in> fmla_set t \<Longrightarrow> n < length (collect_subfmlas r phis)"
proof (induction r "(q0, qf, phis)" arbitrary: q0 qf phis t rule: build_nfa_impl.induct)
  case (2 \<phi> q0 qf phis)
  then show ?case
    using pos_sound pos_complete by (force split: option.splits)
next
  case (3 r s q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
next
  case (4 r s q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
next
  case (5 r q0 qf phis)
  then show ?case
    using length_collect_subfmlas dual_order.strict_trans1 by fastforce
qed auto

context MDL
begin

definition "IH r q0 qf phis transs bss bs i \<equiv>
  transs = build_nfa_impl r (q0, qf, phis) \<and>
  qf \<notin> NFA.SQ q0 (build_nfa_impl r (q0, qf, phis)) \<and>
  (\<forall>k < length (collect_subfmlas r phis).
    (bs ! k \<longleftrightarrow> sat (i + length bss) (collect_subfmlas r phis ! k))) \<and>
  (\<forall>j < length bss. \<forall>k < length (collect_subfmlas r phis).
    ((bss ! j) ! k \<longleftrightarrow> sat (i + j) (collect_subfmlas r phis ! k)))"

lemma nfa_correct: "IH r q0 qf phis transs bss bs i \<Longrightarrow>
  NFA.run_accept q0 qf transs {q0} bss bs \<longleftrightarrow> (i, i + length bss) \<in> match r"
proof (induct r arbitrary: q0 qf phis transs bss bs i rule: regex_induct)
  case Wild
  interpret base: nfa q0 qf "build_nfa_impl Wild (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil Wild
    unfolding IH_def NFA.Q_def
    by auto
  have "\<And>cs q. \<not>base.step_eps cs q0 q"
    unfolding NFA.step_eps_def
    by (auto split: transition.splits)
  then have base_eps: "\<And>cs. base.eps_closure_set {q0} cs = {q0}"
    using NFA.eps_closure_set_step_id by fastforce
  have base_delta: "\<And>cs. base.delta {q0} cs = {qf}"
    unfolding NFA.delta_def base_eps NFA.step_wild_set_def NFA.step_wild_def
    using base.q0_sub_SQ
    by auto
  show ?case
  proof (cases bss)
    case Nil
    show ?thesis
      unfolding Nil
      using NFA.run_accept_Nil NFA.accept_def base_eps
      using base.qf_not_in_SQ base.q0_sub_SQ
      using IH_def Wild by auto
  next
    case (Cons cs css)
    then have bss_split: "bss = cs # css"
      by simp
    show ?thesis
    proof (cases css)
      case Nil
      show ?thesis
        using Cons Nil NFA.run_accept_Cons NFA.run_accept_Nil base_delta NFA.accept_def
        using NFA.eps_closure_set_refl
        using IH_def Wild by fastforce
    next
      case (Cons ds dss)
      show ?thesis
        using bss_split Cons NFA.run_accept_Cons base_delta base.delta_qf
        using NFA.run_accept_empty
        using IH_def Wild by auto
    qed
  qed
next
  case (Test \<phi>)
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Test \<phi>) (q0, qf, phis))"
    using Test unfolding IH_def by auto
  interpret base: nfa q0 qf "build_nfa_impl (Test \<phi>) (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def
    by fast+
  define n where "n \<equiv> case pos \<phi> phis of Some n \<Rightarrow> n | _ \<Rightarrow> length phis"
  then have collect: "n < length (collect_subfmlas (Test \<phi>) phis)"
    "(collect_subfmlas (Test \<phi>) phis) ! n = \<phi>"
    using pos_sound pos_complete by (force split: option.splits)+
  have base_step: "\<And>cs q. base.step_eps cs q0 q \<longleftrightarrow> cs ! n \<and> q = qf"
    unfolding NFA.step_eps_def using n_def base.q0_sub_SQ
    by (auto split: option.splits)
  show ?case
  proof (cases bss)
    case Nil
    show ?thesis
    proof (cases "bs ! n")
      case True
      then have sat_phi: "sat i \<phi>"
        using Test(1)[unfolded IH_def Nil] collect by auto
      have "\<And>q. base.step_eps bs q0 q \<longleftrightarrow> q = qf"
        using True base_step by auto
      then have "base.eps_closure_set {q0} bs = {q0, qf}"
        using NFA.eps_closure_set_unfold base.eps_closure_set_qf by blast
      with sat_phi show ?thesis
        using Nil NFA.run_accept_Nil NFA.accept_def Test
        by (auto simp: IH_def)
    next
      case False
      then have sat_phi: "\<not>sat i \<phi>"
        using Test(1)[unfolded IH_def Nil] collect by auto
      have "\<And>q. \<not>base.step_eps bs q0 q"
        using False base_step by auto
      then have "base.eps_closure_set {q0} bs = {q0}"
        using NFA.eps_closure_set_step_id by fastforce
      with sat_phi show ?thesis
        unfolding Nil NFA.run_accept_Nil NFA.accept_def
        using base.q0_sub_SQ base.qf_not_in_SQ Test
        by (auto simp: IH_def)
    qed
  next
    case (Cons cs css)
    then show ?thesis
    proof (cases "cs ! n")
      case True
      then have "\<And>q. base.step_eps cs q0 q \<longleftrightarrow> q = qf"
        using base_step by auto
      then have "base.eps_closure_set {q0} cs = {q0, qf}"
        using NFA.eps_closure_set_unfold base.eps_closure_set_qf by blast
      then have base_delta: "base.delta {q0} cs = {}"
        unfolding NFA.delta_def NFA.step_wild_set_def NFA.step_wild_def
        using base.q0_sub_SQ base.qf_not_in_SQ by (auto split: option.splits)
      show ?thesis
        using NFA.run_accept_empty Test Cons NFA.run_accept_Cons base_delta
        by (auto simp: IH_def)
    next
      case False
      then have "\<And>q. \<not>base.step_eps cs q0 q"
        using base_step by auto
      then have "base.eps_closure_set {q0} cs = {q0}"
        using NFA.eps_closure_set_step_id by fastforce
      then have base_delta: "base.delta {q0} cs = {}"
        unfolding NFA.delta_def NFA.step_wild_set_def NFA.step_wild_def
        using base.q0_sub_SQ by (auto split: option.splits)
      show ?thesis
        using NFA.run_accept_empty Cons NFA.run_accept_Cons base_delta Test
        by (auto simp: IH_def)
    qed
  qed
next
  case (Plus r s)
  obtain phis' where collect: "collect_subfmlas (Plus r s) phis =
    collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Plus r s) (q0, qf, phis))"
    using Plus unfolding IH_def by auto
  interpret base: nfa q0 qf "build_nfa_impl (Plus r s) (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt by fast+
  interpret left: nfa "q0 + 1" qf "build_nfa_impl r (q0 + 1, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  interpret right: nfa "q0 + 1 + state_cnt r" qf
    "build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  from Plus(3) have "IH r (q0 + 1) qf phis (build_nfa_impl r (q0 + 1, qf, phis)) bss bs i"
    unfolding IH_def collect
    using left.qf_not_in_SQ
    by (auto simp: nth_append)
  then have left_IH: "left.run_accept {q0 + 1} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match r"
    using Plus(1) build_nfa_impl_state_cnt
    by auto
  have "IH s (q0 + 1 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)) bss bs i"
    using right.qf_not_in_SQ IH_def Plus
    by auto
  then have right_IH: "right.run_accept {q0 + 1 + state_cnt r} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match s"
    using Plus(2) build_nfa_impl_state_cnt
    by auto
  interpret cong: nfa_cong_Plus q0 "q0 + 1" "q0 + 1 + state_cnt r" qf qf qf
    "build_nfa_impl (Plus r s) (q0, qf, phis)" "build_nfa_impl r (q0 + 1, qf, phis)"
    "build_nfa_impl s (q0 + 1 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    unfolding NFA.SQ_def build_nfa_impl_state_cnt
      NFA.step_eps_def NFA.step_wild_def
    by (auto simp add: nth_append build_nfa_impl_state_cnt)
  show ?case
    using cong.run_accept_cong left_IH right_IH Plus
    by (auto simp: IH_def)
next
  case (Times r s)
  obtain phis' where collect: "collect_subfmlas (Times r s) phis =
    collect_subfmlas r phis @ phis'"
    using collect_subfmlas_app by auto
  have transs_def: "transs = build_nfa_impl (Times r s) (q0, qf, phis)"
    using Times unfolding IH_def by auto
  have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Times r s) (q0, qf, phis))"
    using Times unfolding IH_def by auto
  interpret base: nfa q0 qf "build_nfa_impl (Times r s) (q0, qf, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt by fast+
  interpret left: nfa "q0" "q0 + state_cnt r" "build_nfa_impl r (q0, q0 + state_cnt r, phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  interpret right: nfa "q0 + state_cnt r" qf
    "build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
    unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
    by fastforce+
  from Times(3) have left_IH: "IH r q0 (q0 + state_cnt r) phis
    (build_nfa_impl r (q0 , q0 + state_cnt r, phis)) bss bs i"
    unfolding IH_def collect
    using left.qf_not_in_SQ
    by (auto simp: nth_append)
  from Times(3) have left_IH_take: "\<And>n. n < length bss \<Longrightarrow>
    IH r q0 (q0 + state_cnt r) phis
    (build_nfa_impl r (q0, q0 + state_cnt r, phis)) (take n bss) (hd (drop n bss)) i"
    unfolding IH_def collect
    using left.qf_not_in_SQ
    by (auto simp: nth_append min_absorb2 hd_drop_conv_nth)
  have left_IH_match: "left.run_accept {q0} bss bs \<longleftrightarrow>
    (i, i + length bss) \<in> match r"
    using Times(1) build_nfa_impl_state_cnt left_IH
    by auto
  have left_IH_match_take: "\<And>n. n < length bss \<Longrightarrow>
    left.run_accept {q0} (take n bss) (hd (drop n bss)) \<longleftrightarrow> (i, i + n) \<in> match r"
    using Times(1) build_nfa_impl_state_cnt left_IH_take
    by (fastforce simp add: nth_append min_absorb2)
  have "IH s (q0 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)) bss bs i"
    using right.qf_not_in_SQ IH_def Times
    by auto
  then have right_IH: "\<And>n. n \<le> length bss \<Longrightarrow> IH s (q0 + state_cnt r) qf (collect_subfmlas r phis)
    (build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)) (drop n bss) bs (i + n)"
    unfolding IH_def
    by (auto simp: nth_append add.assoc)
  have right_IH_match: "\<And>n. n \<le> length bss \<Longrightarrow>
    right.run_accept {q0 + state_cnt r} (drop n bss) bs \<longleftrightarrow> (i + n, i + length bss) \<in> match s"
    using Times(2)[OF right_IH] build_nfa_impl_state_cnt
    by (auto simp: IH_def)
  interpret cong: nfa_cong_Times q0 "q0 + state_cnt r" qf
    "build_nfa_impl (Times r s) (q0, qf, phis)"
    "build_nfa_impl r (q0, q0 + state_cnt r, phis)"
    "build_nfa_impl s (q0 + state_cnt r, qf, collect_subfmlas r phis)"
    apply unfold_locales
    using NFA.Q_def NFA.SQ_def NFA.step_eps_def NFA.step_wild_def build_nfa_impl_state_set
    by (fastforce simp add: nth_append build_nfa_impl_state_cnt build_nfa_impl_not_Nil
        state_cnt_pos)+
  have right_IH_Nil: "right.run_accept {q0 + state_cnt r} [] bs \<longleftrightarrow>
    (i + length bss, i + length bss) \<in> match s"
    using right_IH_match
    by fastforce
  show ?case
    unfolding match_Times transs_def cong.run_accept_cong left_IH_match right_IH_Nil
    using left_IH_match_take right_IH_match less_imp_le_nat le_eq_less_or_eq
    by auto
next
  case (Star r)
  then show ?case
  proof (induction "length bss" arbitrary: bss bs i rule: nat_less_induct)
    case 1
    have transs_def: "transs = build_nfa_impl (Star r) (q0, qf, phis)"
      using 1 unfolding IH_def by auto
    have qf_not_in_SQ: "qf \<notin> NFA.SQ q0 (build_nfa_impl (Star r) (q0, qf, phis))"
      using 1 unfolding IH_def by auto
    interpret base: nfa q0 qf "build_nfa_impl (Star r) (q0, qf, phis)"
      apply unfold_locales
      using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
      unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
      by fast+
    interpret left: nfa "q0 + 1" q0 "build_nfa_impl r (q0 + 1, q0, phis)"
      apply unfold_locales
      using build_nfa_impl_state_set build_nfa_impl_not_Nil qf_not_in_SQ
      unfolding NFA.Q_def NFA.SQ_def build_nfa_impl_state_cnt
      by fastforce+
    from 1(3) have left_IH: "IH r (q0 + 1) q0 phis (build_nfa_impl r (q0 + 1, q0, phis)) bss bs i"
      using left.qf_not_in_SQ
      unfolding IH_def
      by (auto simp add: nth_append)
    from 1(3) have left_IH_take: "\<And>n. n < length bss \<Longrightarrow>
      IH r (q0 + 1) q0 phis (build_nfa_impl r (q0 + 1, q0, phis)) (take n bss) (hd (drop n bss)) i"
      using left.qf_not_in_SQ
      unfolding IH_def
      by (auto simp add: nth_append min_absorb2 hd_drop_conv_nth)
    have left_IH_match: "left.run_accept {q0 + 1} bss bs \<longleftrightarrow>
      (i, i + length bss) \<in> match r"
      using 1(2) left_IH
      unfolding build_nfa_impl_state_cnt NFA.SQ_def
      by auto
    have left_IH_match_take: "\<And>n. n < length bss \<Longrightarrow>
      left.run_accept {q0 + 1} (take n bss) (hd (drop n bss)) \<longleftrightarrow>
      (i, i + n) \<in> match r"
      using 1(2) left_IH_take
      unfolding build_nfa_impl_state_cnt NFA.SQ_def
      by (fastforce simp add: nth_append min_absorb2)
    interpret cong: nfa_cong_Star q0 "q0 + 1" qf
      "build_nfa_impl (Star r) (q0, qf, phis)"
      "build_nfa_impl r (q0 + 1, q0, phis)"
      apply unfold_locales
      unfolding NFA.SQ_def build_nfa_impl_state_cnt NFA.step_eps_def NFA.step_wild_def
      by (auto simp add: nth_append build_nfa_impl_state_cnt)
    show ?case
      using cong.run_accept_Nil
    proof (cases bss)
      case Nil
      show ?thesis
        unfolding transs_def Nil
        using cong.run_accept_Nil run_Nil run_accept_Nil
        by auto
    next
      case (Cons cs css)
      have aux: "\<And>n j x P. n < x \<Longrightarrow> j < x - n \<Longrightarrow> (\<forall>j < Suc x. P j) \<Longrightarrow> P (Suc (n + j))"
        by auto
      from 1(3) have star_IH: "\<And>n. n < length css \<Longrightarrow>
        IH (Star r) q0 qf phis transs (drop n css) bs (i + n + 1)"
        unfolding Cons IH_def
        using aux[of _ _ _ "\<lambda>j. \<forall>k<length (collect_subfmlas r phis).
          (cs # css) ! j ! k = sat (i + j) (collect_subfmlas r phis ! k)"]
        by (auto simp add: nth_append add.assoc)
      have IH_inst: "\<And>xs i. length xs \<le> length css \<Longrightarrow> IH (Star r) q0 qf phis transs xs bs i \<longrightarrow>
        (base.run_accept {q0} xs bs \<longleftrightarrow> (i, i + length xs) \<in> match (Star r))"
        using 1
        unfolding Cons
        by (auto simp add: nth_append less_Suc_eq_le transs_def)
      have "\<And>n. n < length css \<Longrightarrow> base.run_accept {q0} (drop n css) bs \<longleftrightarrow>
        (i + n + 1, i + length (cs # css)) \<in> match (Star r)"
      proof -
        fix n
        assume assm: "n < length css"
        then show "base.run_accept {q0} (drop n css) bs \<longleftrightarrow>
          (i + n + 1, i + length (cs # css)) \<in> match (Star r)"
          using IH_inst[of "drop n css" "i + n + 1"] star_IH
          by (auto simp add: nth_append)
      qed
      then show ?thesis
        using match_Star length_Cons Cons cong.run_accept_cong_Cons
        using cong.run_accept_Nil left_IH_match left_IH_match_take
        apply (auto simp add: Cons transs_def)
         apply (metis Suc_less_eq add_Suc_right drop_Suc_Cons less_imp_le_nat take_Suc_Cons)
        apply (metis Suc_less_eq add_Suc_right drop_Suc_Cons le_eq_less_or_eq lessThan_iff
            take_Suc_Cons)
        done
    qed
  qed
qed

end

context
  fixes args :: "(bool iarray, nat set, 'd :: timestamp, 't, 'e) args"
begin

abbreviation "reach_w \<equiv> reach_window args"

qualified definition "in_win = init_window args"

definition valid_window_matchP :: "'d \<I> \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow>
  ('d \<times> bool iarray) list \<Rightarrow> nat \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow> bool" where
  "valid_window_matchP I t0 sub rho j w \<longleftrightarrow> j = w_j w \<and>
    valid_window args t0 sub rho w \<and>
    reach_w t0 sub rho (w_i w, w_ti w, w_si w, w_j w, w_tj w, w_sj w) \<and>
    (case w_read_t args (w_tj w) of None \<Rightarrow> True
    | Some t \<Rightarrow> (\<forall>l < w_i w. ts_at rho l + left I \<le> t))"

lemma valid_window_matchP_reach_tj: "valid_window_matchP I t0 sub rho i w \<Longrightarrow>
  reach_sub (w_run_t args) t0 (map fst rho) (w_tj w)"
  using reach_window_run_tj
  by (fastforce simp: valid_window_matchP_def simp del: reach_window.simps)

lemma valid_window_matchP_reach_sj: "valid_window_matchP I t0 sub rho i w \<Longrightarrow>
  reach_sub (w_run_sub args) sub (map snd rho) (w_sj w)"
  using reach_window_run_sj
  by (fastforce simp: valid_window_matchP_def simp del: reach_window.simps)

lemma valid_window_matchP_len_rho: "valid_window_matchP I t0 sub rho i w \<Longrightarrow> length rho = i"
  by (auto simp: valid_window_matchP_def)

definition "matchP_loop_cond I t = (\<lambda>w. w_i w < w_j w \<and> the (w_read_t args (w_ti w)) + left I \<le> t)"
definition "matchP_loop_inv I t0 sub rho j0 tj0 sj0 t =
  (\<lambda>w. valid_window args t0 sub rho w \<and>
    w_j w = j0 \<and> w_tj w = tj0 \<and> w_sj w = sj0 \<and> (\<forall>l < w_i w. ts_at rho l + left I \<le> t))"

fun ex_key :: "('c, 'd) mmap \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow>
  ('c \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<times> 'b, bool) mapping \<Rightarrow> 'b \<Rightarrow> (bool \<times> ('c \<times> 'b, bool) mapping)" where
  "ex_key [] time accept ac bs = (False, ac)"
| "ex_key ((q, t) # qts) time accept ac bs = (if time t then
    (case cac accept ac q bs of (\<beta>, ac') \<Rightarrow>
    if \<beta> then (True, ac') else ex_key qts time accept ac' bs)
  else ex_key qts time accept ac bs)"

lemma ex_key_sound:
  assumes inv: "\<And>q bs. case Mapping.lookup ac (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> accept q bs = v"
  and distinct: "distinct (map fst qts)"
  and eval: "ex_key qts time accept ac bs = (b, ac')"
  shows "b = (\<exists>q \<in> mmap_keys qts. time (the (mmap_lookup qts q)) \<and> accept q bs) \<and>
    (\<forall>q bs. case Mapping.lookup ac' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> accept q bs = v)"
  using assms
proof (induction qts arbitrary: ac)
  case (Cons a qts)
  obtain q t where qt_def: "a = (q, t)"
    by fastforce
  show ?case
  proof (cases "time t")
    case True
    note time_t = True
    obtain \<beta> ac'' where ac''_def: "cac accept ac q bs = (\<beta>, ac'')"
      by fastforce
    have accept: "\<beta> = accept q bs" "\<And>q bs. case Mapping.lookup ac'' (q, bs) of None \<Rightarrow> True
      | Some v \<Rightarrow> accept q bs = v"
      using ac''_def Cons(2)
      by (fastforce simp: cac_def Let_def Mapping.lookup_update' split: option.splits if_splits)+
    show ?thesis
    proof (cases \<beta>)
      case True
      then show ?thesis
        using accept(2) time_t Cons(4)
        by (auto simp: qt_def mmap_keys_def accept(1) mmap_lookup_def ac''_def)
    next
      case False
      have ex_key: "ex_key qts time accept ac'' bs = (b, ac')"
        using Cons(4) time_t False
        by (auto simp: qt_def ac''_def)
      show ?thesis
        using Cons(1)[OF accept(2) _ ex_key] False[unfolded accept(1)] Cons(3)
        by (auto simp: mmap_keys_def mmap_lookup_def qt_def)
    qed
  next
    case False
    have ex_key: "ex_key qts time accept ac bs = (b, ac')"
      using Cons(4) False
      by (auto simp: qt_def)
    show ?thesis
      using Cons(1)[OF Cons(2) _ ex_key] False Cons(3)
      by (auto simp: mmap_keys_def mmap_lookup_def qt_def)
  qed
qed (auto simp: mmap_keys_def)

fun eval_matchP :: "'d \<I> \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow>
  (('d \<times> bool) \<times> (bool iarray, nat set, 'd, 't, 'e) window) option" where
  "eval_matchP I w =
    (case w_read_t args (w_tj w) of None \<Rightarrow> None
    | Some t \<Rightarrow> (case w_read_sub args (w_sj w) of None \<Rightarrow> None
    | Some b \<Rightarrow>
      let w' = while (matchP_loop_cond I t) (adv_start args) w;
      (\<beta>, ac') = ex_key (w_e w') (\<lambda>t'. t \<le> t' + right I) (w_accept args) (w_ac w') b;
      (\<beta>', ac'') = (if \<beta> then (True, ac')
        else if mem t t I then cac (w_accept args) ac' {0} b
        else (False, ac')) in
      Some ((t, \<beta>'), adv_end args (w'\<lparr>w_ac := ac''\<rparr>))))"

definition valid_window_matchF :: "'d \<I> \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> ('d \<times> bool iarray) list \<Rightarrow> nat \<Rightarrow>
  (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow> bool" where
  "valid_window_matchF I t0 sub rho i w \<longleftrightarrow> i = w_i w \<and>
    valid_window args t0 sub rho w \<and>
    reach_w t0 sub rho (w_i w, w_ti w, w_si w, w_j w, w_tj w, w_sj w) \<and>
    (\<forall>l \<in> {w_i w..<w_j w}. ts_at rho l \<le> ts_at rho i + right I)"

lemma valid_window_matchF_reach_tj: "valid_window_matchF I t0 sub rho i w \<Longrightarrow>
  reach_sub (w_run_t args) t0 (map fst rho) (w_tj w)"
  using reach_window_run_tj
  by (fastforce simp: valid_window_matchF_def simp del: reach_window.simps)

lemma valid_window_matchF_reach_sj: "valid_window_matchF I t0 sub rho i w \<Longrightarrow>
  reach_sub (w_run_sub args) sub (map snd rho) (w_sj w)"
  using reach_window_run_sj
  by (fastforce simp: valid_window_matchF_def simp del: reach_window.simps)

definition "matchF_loop_cond I t =
  (\<lambda>w. case w_read_t args (w_tj w) of None \<Rightarrow> False
  | Some t' \<Rightarrow> t' \<le> t + right I \<and> w_read_sub args (w_sj w) \<noteq> None)"
definition "matchF_loop_inv I t0 sub rho i ti si tjm sjm =
  (\<lambda>w. valid_window args t0 sub (take (w_j w) rho) w \<and>
  w_i w = i \<and> w_ti w = ti \<and> w_si w = si \<and>
  reach_window args t0 sub rho (w_j w, w_tj w, w_sj w, length rho, tjm, sjm) \<and>
  (\<forall>l \<in> {w_i w..<w_j w}. ts_at rho l \<le> ts_at rho i + right I))"

definition "matchF_loop_inv' t0 sub rho i ti si j tj sj =
  (\<lambda>w. w_i w = i \<and> w_ti w = ti \<and> w_si w = si \<and>
    (\<exists>rho'. valid_window args t0 sub (rho @ rho') w \<and>
    reach_window args t0 sub (rho @ rho') (j, tj, sj, w_j w, w_tj w, w_sj w)))"

fun eval_matchF :: "'d \<I> \<Rightarrow> (bool iarray, nat set, 'd, 't, 'e) window \<Rightarrow>
  (('d \<times> bool) \<times> (bool iarray, nat set, 'd, 't, 'e) window) option" where
  "eval_matchF I w =
    (case w_read_t args (w_ti w) of None \<Rightarrow> None
    | Some t \<Rightarrow> 
      let w' = while (matchF_loop_cond I t) (adv_end args) w in
      (case w_read_t args (w_tj w') of None \<Rightarrow> None
      | Some t' \<Rightarrow> if t' \<le> t + right I then None else
        let \<beta> = (case snd (the (mmap_lookup (w_s w') {0})) of None \<Rightarrow> False
          | Some tstp \<Rightarrow> t + left I \<le> fst tstp) in
        Some ((t, \<beta>), adv_start args w')))"

end

locale MDL_window = MDL \<sigma>
  for \<sigma> :: "('a, 'd :: timestamp) trace" +
  fixes r :: "('a, 'd :: timestamp) regex"
    and t0 :: 't
    and sub :: 'e
    and args :: "(bool iarray, nat set, 'd, 't, 'e) args"
  assumes init_def: "w_init args = {0 :: nat}"
    and step_def: "w_step args =
      NFA.delta' (IArray (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r)"
    and accept_def: "w_accept args =
      NFA.accept' (IArray (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r)"
    and run_t_sound: "reach_sub (w_run_t args) t0 ts t \<Longrightarrow>
      w_run_t args t = Some (t', x) \<Longrightarrow> x = \<tau> \<sigma> (length ts)"
    and run_sub_sound: "reach_sub (w_run_sub args) sub bs s \<Longrightarrow>
      w_run_sub args s = Some (s', b) \<Longrightarrow>
      b = IArray (map (sat (length bs)) (collect_subfmlas r []))"
    and run_t_read: "w_run_t args t = Some (t', x) \<Longrightarrow> w_read_t args t = Some x"
    and read_t_run: "w_read_t args t = Some x \<Longrightarrow> \<exists>t'. w_run_t args t = Some (t', x)"
    and run_sub_read: "w_run_sub args s = Some (s', y) \<Longrightarrow> w_read_sub args s = Some y"
    and read_sub_run: "w_read_sub args s = Some y \<Longrightarrow> \<exists>s'. w_run_sub args s = Some (s', y)"
begin

definition "qf = state_cnt r"
definition "transs = build_nfa_impl r (0, qf, [])"

abbreviation "init \<equiv> w_init args"
abbreviation "step \<equiv> w_step args"
abbreviation "accept \<equiv> w_accept args"
abbreviation "run \<equiv> NFA.run' (IArray transs) qf"
abbreviation "wacc \<equiv> Window.acc (w_step args) (w_accept args)"
abbreviation "rw \<equiv> reach_window args"

abbreviation "valid_matchP \<equiv> valid_window_matchP args"
abbreviation "eval_mP \<equiv> eval_matchP args"
abbreviation "matchP_inv \<equiv> matchP_loop_inv args"
abbreviation "matchP_cond \<equiv> matchP_loop_cond args"

abbreviation "valid_matchF \<equiv> valid_window_matchF args"
abbreviation "eval_mF \<equiv> eval_matchF args"
abbreviation "matchF_inv \<equiv> matchF_loop_inv args"
abbreviation "matchF_inv' \<equiv> matchF_loop_inv' args"
abbreviation "matchF_cond \<equiv> matchF_loop_cond args"

lemma run_t_sound':
  assumes "reach_sub (w_run_t args) t0 ts t" "i < length ts"
  shows "ts ! i = \<tau> \<sigma> i"
proof -
  obtain t' t'' where t'_def: "reach_sub (w_run_t args) t0 (take i ts) t'"
    "w_run_t args t' = Some (t'', ts ! i)"
    using reach_sub_split[OF assms]
    by auto
  show ?thesis
    using run_t_sound[OF t'_def] assms(2)
    by (simp add: min.absorb2)
qed

lemma run_sub_sound':
  assumes "reach_sub (w_run_sub args) sub bs s" "i < length bs"
  shows "bs ! i = IArray (map (sat i) (collect_subfmlas r []))"
proof -
  obtain s' s'' where s'_def: "reach_sub (w_run_sub args) sub (take i bs) s'"
    "w_run_sub args s' = Some (s'', bs ! i)"
    using reach_sub_split[OF assms]
    by auto
  show ?thesis
    using run_sub_sound[OF s'_def] assms(2)
    by (simp add: min.absorb2)
qed

lemma run_ts: "reach_sub (w_run_t args) t ts t' \<Longrightarrow> t = t0 \<Longrightarrow> chain_le ts"
proof (induction t ts t' rule: reach_sub_rev_induct)
  case (2 s s' v vs s'')
  show ?case
  proof (cases vs rule: rev_cases)
    case (snoc zs z)
    show ?thesis
      using 2(3)[OF 2(4)]
      using chain_le_app[OF _ \<tau>_mono[of "length zs" "Suc (length zs)" \<sigma>]]
        run_t_sound'[OF reach_sub_app[OF 2(1,2), unfolded 2(4)], of "length zs"]
        run_t_sound'[OF reach_sub_app[OF 2(1,2), unfolded 2(4)], of "Suc (length zs)"]
      unfolding snoc
      by (auto simp: nth_append)
  qed (auto intro: chain_le.intros)
qed (auto intro: chain_le.intros)

lemma ts_at_tau: "reach_sub (w_run_t args) t0 (map fst rho) t \<Longrightarrow> i < length rho \<Longrightarrow>
  ts_at rho i = \<tau> \<sigma> i"
  using run_t_sound'
  unfolding ts_at_def
  by fastforce

lemma length_bs_at: "reach_sub (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i < length rho \<Longrightarrow>
  IArray.length (bs_at rho i) = length (collect_subfmlas r [])"
  using run_sub_sound'
  unfolding bs_at_def
  by fastforce

lemma bs_at_nth: "reach_sub (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i < length rho \<Longrightarrow>
  n < IArray.length (bs_at rho i) \<Longrightarrow>
  IArray.sub (bs_at rho i) n \<longleftrightarrow> sat i (collect_subfmlas r [] ! n)"
  using run_sub_sound'
  unfolding bs_at_def
  by fastforce

lemma ts_at_mono: "\<And>i j. reach_sub (w_run_t args) t0 (map fst rho) t \<Longrightarrow>
  i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
  using ts_at_tau
  by fastforce

lemma steps_is_run: "steps (w_step args) rho q ij = run q (sub_bs rho ij)"
  unfolding NFA.run'_def steps_def step_def transs_def qf_def ..

lemma acc_is_accept: "wacc rho q (i, j) = w_accept args (run q (sub_bs rho (i, j)))
  (bs_at rho j)"
  unfolding acc_def steps_is_run by auto

lemma iarray_list_of: "IArray (IArray.list_of xs) = xs"
  by (cases xs) auto

lemma map_iarray_list_of: "map IArray (map IArray.list_of bss) = bss"
  using iarray_list_of
  by (induction bss) auto

lemma acc_match:
  fixes ts :: "'d list"
  shows "reach_sub (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow>
    wacc rho {0} (i, j) \<longleftrightarrow> (i, j) \<in> match r"
proof -
  assume assms: "reach_sub (w_run_sub args) sub (map snd rho) s" "i \<le> j" "j < length rho"
  have j_eq: "j = i + length (sub_bs rho (i, j))"
    using assms by auto
  have IH: "IH r 0 qf [] transs (map IArray.list_of (sub_bs rho (i, j)))
    (IArray.list_of (bs_at rho j)) i"
    unfolding IH_def transs_def qf_def NFA.SQ_def build_nfa_impl_state_cnt
    using assms run_sub_sound bs_at_nth length_bs_at by fastforce
  interpret NFA_array: nfa_array transs "IArray transs" qf
    by unfold_locales (auto simp: qf_def transs_def build_nfa_impl_state_cnt)
  show ?thesis
    using nfa_correct[OF IH, unfolded NFA.run_accept_def]
    using NFA_array.accept'_eq[of "bs_at rho j" "IArray.list_of (bs_at rho j)"]
      NFA_array.run'_eq[of "sub_bs rho (i, j)" "map IArray.list_of (sub_bs rho (i, j))"]
    unfolding acc_is_accept j_eq[symmetric] accept_def acc_def length_map steps_is_run
    by (simp add: transs_def qf_def iarray_list_of map_iarray_list_of)
qed

lemma accept_match:
  fixes ts :: "'d list"
  shows "reach_sub (w_run_sub args) sub (map snd rho) s \<Longrightarrow> i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow>
  w_accept args (steps (w_step args) rho {0} (i, j)) (bs_at rho j) \<longleftrightarrow> (i, j) \<in> match r"
  using acc_match acc_is_accept steps_is_run
  by metis

lemma drop_take_drop: "i \<le> j \<Longrightarrow> j \<le> length rho \<Longrightarrow> drop i (take j rho) @ drop j rho = drop i rho"
  apply (induction i arbitrary: j rho)
  by auto (metis append_take_drop_id diff_add drop_drop drop_take)

lemma take_Suc: "drop n xs = y # ys \<Longrightarrow> take n xs @ [y] = take (Suc n) xs"
  by (metis drop_all list.distinct(1) list.sel(1) not_less take_hd_drop)

lemma valid_init_matchP: "valid_matchP I t0 sub [] 0 (init_window args t0 sub)"
  using valid_init_window
  by (fastforce simp: valid_window_matchP_def Let_def intro: reach_sub.intros split: option.splits)

lemma valid_init_matchF: "valid_matchF I t0 sub [] 0 (init_window args t0 sub)"
  using valid_init_window
  by (fastforce simp: valid_window_matchF_def Let_def intro: reach_sub.intros split: option.splits)

lemma valid_eval_matchP:
  assumes valid_before': "valid_matchP I t0 sub rho j w"
    and before_end: "w_run_t args (w_tj w) = Some (tj''', t)"
    "w_run_sub args (w_sj w) = Some (sj''', b)"
  shows "\<exists>w'. eval_mP I w = Some ((\<tau> \<sigma> j, sat j (MatchP I r)), w') \<and>
    t = \<tau> \<sigma> j \<and> valid_matchP I t0 sub (rho @ [(t, b)]) (Suc j) w'"
proof -
  define st where "st = w_st w"
  define i where "i = w_i w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "rw t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    "valid_s init step st accept rho i i j s"
    "j = w_j w" "i \<le> j"
    using valid_before'[unfolded valid_window_matchP_def] ti_def
      si_def i_def tj_def sj_def s_def e_def
    by (auto simp: valid_window_def Let_def init_def step_def st_def accept_def
        split: option.splits)
  note read_t_def = run_t_read[OF before_end(1)]
  have t_props: "\<forall>l < i. ts_at rho l + left I \<le> t"
    using valid_before'[unfolded valid_window_matchP_def read_t_def]
    unfolding i_def
    by auto
  note read_sub_def = run_sub_read[OF before_end(2)]
  define rho' where "rho' = rho @ [(t, b)]"
  note rw_app = reach_window_app[OF valid_before(1)
      before_end[unfolded tj_def[symmetric] sj_def[symmetric]]]
  have reach_sub': "reach_sub (w_run_t args) t0 (map fst rho') tj'''"
    using reach_window_run_tj[OF rw_app] valid_before(6)
    by (auto simp: rho'_def)
  have length_rho: "length rho = j"
    using valid_before by auto
  have reach_sub_tj: "reach_sub (w_run_t args) t0 (map fst rho) tj"
    using valid_before reach_sub_trans by fastforce
  then have reach_sub_tj': "reach_sub (w_run_t args) t0 (map fst rho') tj'''"
    using reach_sub_app before_end by (fastforce simp: rho'_def tj_def)
  have "reach_sub (w_run_sub args) sub (map snd rho) sj"
    using valid_before reach_sub_trans by fastforce
  then have reach_sub_sj': "reach_sub (w_run_sub args) sub (map snd rho') sj'''"
    using reach_sub_app before_end by (fastforce simp: rho'_def sj_def)
  have tj_def': "t = \<tau> \<sigma> j" "t = ts_at rho' j"
    using run_t_sound'[OF reach_sub_tj', of j]
    by (auto simp: length_rho nth_append ts_at_def rho'_def)
  have bj_def: "b = bs_at rho' j"
    using run_sub_sound'[OF reach_sub_sj', of j]
    by (auto simp: length_rho nth_append bs_at_def rho'_def)
  have j_len_rho': "j < length rho'"
    by (auto simp: length_rho rho'_def)
  define w' where loop_def: "w' = while (matchP_cond I t) (adv_start args) w"
  have inv_before: "matchP_inv I t0 sub rho j tj sj t w"
    using valid_before valid_before'[unfolded valid_window_matchP_def] t_props
    by (auto simp add: matchP_loop_inv_def read_t_def i_def tj_def sj_def
        split: option.splits)
  have loop: "matchP_inv I t0 sub rho j tj sj t w' \<and> \<not> matchP_cond I t w'"
    unfolding loop_def
  proof (rule while_rule_lemma[of "matchP_inv I t0 sub rho j tj sj t"])
    fix w_cur :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchP_inv I t0 sub rho j tj sj t w_cur" "matchP_cond I t w_cur"
    define st_cur where "st_cur = w_st w_cur"
    define i_cur where "i_cur = w_i w_cur"
    define ti_cur where "ti_cur = w_ti w_cur"
    define si_cur where "si_cur = w_si w_cur"
    define s_cur where "s_cur = w_s w_cur"
    define e_cur where "e_cur = w_e w_cur"
    have valid_loop: "rw t0 sub rho (i_cur, ti_cur, si_cur, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e_cur q = sup_leadsto init step rho i_cur j q"
    "valid_s init step st_cur accept rho i_cur i_cur j s_cur"
    "j = w_j w_cur"
      using assms(1)[unfolded matchP_loop_inv_def valid_window_matchP_def] valid_before(6)
        ti_cur_def si_cur_def i_cur_def s_cur_def e_cur_def
      by (auto simp: valid_window_def Let_def init_def step_def st_cur_def accept_def
          split: option.splits)
    obtain ti'_cur si'_cur t_cur b_cur where run_si_cur:
      "w_run_t args ti_cur = Some (ti'_cur, t_cur)" "w_run_sub args si_cur = Some (si'_cur, b_cur)"
      "t_cur = ts_at rho i_cur" "b_cur = bs_at rho i_cur"
      using assms(2) reach_window_run_si[OF valid_loop(1)] reach_window_run_ti[OF valid_loop(1)]
      unfolding matchP_loop_cond_def valid_loop(5) i_cur_def
      by auto
    have "\<And>l. l < i_cur \<Longrightarrow> ts_at rho l + left I \<le> t"
      using assms(1)
      unfolding matchP_loop_inv_def i_cur_def
      by auto
    then have "\<And>l. l < i_cur + 1 \<Longrightarrow> ts_at rho l + left I \<le> t"
      using assms(2) run_t_read[OF run_si_cur(1), unfolded run_si_cur(3)]
      unfolding matchP_loop_cond_def i_cur_def ti_cur_def
      by (auto simp: less_Suc_eq)
    then show "matchP_inv I t0 sub rho j tj sj t (adv_start args w_cur)"
      using assms i_cur_def valid_adv_start valid_adv_start_bounds
      unfolding matchP_loop_inv_def matchP_loop_cond_def
      by fastforce
  next
    {
      fix w1 w2
      assume lassms: "matchP_inv I t0 sub rho j tj sj t w1" "matchP_cond I t w1"
        "w2 = adv_start args w1"
      define i_cur where "i_cur = w_i w1"
      define ti_cur where "ti_cur = w_ti w1"
      define si_cur where "si_cur = w_si w1"
      have valid_loop: "rw t0 sub rho (i_cur, ti_cur, si_cur, j, tj, sj)" "j = w_j w1"
        using lassms(1)[unfolded matchP_loop_inv_def valid_window_matchP_def] valid_before(6)
          ti_cur_def si_cur_def i_cur_def
        by (auto simp: valid_window_def Let_def)
      obtain ti'_cur si'_cur t_cur b_cur where run_si_cur:
        "w_run_t args ti_cur = Some (ti'_cur, t_cur)"
        "w_run_sub args si_cur = Some (si'_cur, b_cur)"
        using lassms(2) reach_window_run_si[OF valid_loop(1)] reach_window_run_ti[OF valid_loop(1)]
        unfolding matchP_loop_cond_def valid_loop i_cur_def
        by auto
      have w1_ij: "w_i w1 < j" "w_j w1 = j"
        using lassms
        unfolding matchP_loop_inv_def matchP_loop_cond_def
        by auto
      have w2_ij: "w_i w2 = Suc (w_i w1)" "w_j w2 = j"
        using w1_ij lassms(3) run_si_cur(1,2)
        unfolding ti_cur_def si_cur_def
        by (auto simp: adv_start_def Let_def split: option.splits prod.splits if_splits)
      have "w_j w2 - w_i w2 < w_j w1 - w_i w1"
        using w1_ij w2_ij
        by auto
    }
    then have "{(s', s). matchP_inv I t0 sub rho j tj sj t s \<and> matchP_cond I t s \<and>
      s' = adv_start args s} \<subseteq> measure (\<lambda>w. w_j w - w_i w)"
      by auto
    then show "wf {(s', s). matchP_inv I t0 sub rho j tj sj t s \<and> matchP_cond I t s \<and>
      s' = adv_start args s}"
      using wf_measure wf_subset by auto
  qed (auto simp add: inv_before)
  define st' where "st' = w_st w'"
  define ac where "ac = w_ac w'"
  define i' where "i' = w_i w'"
  define ti' where "ti' = w_ti w'"
  define si' where "si' = w_si w'"
  define s' where "s' = w_s w'"
  define e' where "e' = w_e w'"
  have valid_after: "rw t0 sub rho (i', ti', si', j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "distinct (map fst e')"
    "\<forall>q. mmap_lookup e' q = sup_leadsto init step rho i' j q"
    "\<And>q bs. case Mapping.lookup ac (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> accept q bs = v"
    "valid_s init step st' accept rho i' i' j s'" "i' \<le> j" "j \<le> length rho"
    "valid_window args t0 sub rho w'"
    using conjunct1[OF loop] i'_def ti'_def si'_def s'_def e'_def
    unfolding matchP_loop_inv_def
    by (auto simp: valid_window_def Let_def init_def step_def st'_def ac_def accept_def
        split: option.splits)
  note lookup_e' = valid_after(3,5,6)
  obtain \<beta> ac' where ac'_def: "ex_key e' (\<lambda>t'. t \<le> t' + right I)
    (w_accept args) ac b = (\<beta>, ac')"
    by fastforce
  have \<beta>_def: "\<beta> = (\<exists>q\<in>mmap_keys e'. t \<le> the (mmap_lookup e' q) + right I \<and> accept q b)"
    "\<And>q bs. case Mapping.lookup ac' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> accept q bs = v"
    using ex_key_sound[OF valid_after(5) valid_after(3) ac'_def]
    by auto
  obtain \<beta>' ac'' where ac''_def: "(if \<beta> then (True, ac')
    else if mem t t I then cac (w_accept args) ac' {0} b
    else (False, ac')) = (\<beta>', ac'')"
    by fastforce
  have \<beta>'_def: "\<beta>' = ((\<exists>q\<in>mmap_keys e'. t \<le> (the (mmap_lookup e' q)) + right I \<and>
    accept q b) \<or> (mem t t I \<and> accept {0} b))"
    "\<And>q bs. case Mapping.lookup ac'' (q, bs) of None \<Rightarrow> True | Some v \<Rightarrow> accept q bs = v"
    using ac''_def \<beta>_def
    by (fastforce simp: cac_def Let_def Mapping.lookup_update' split: if_splits option.splits)+
  define w'' where adv_end_last: "w'' = adv_end args (w'\<lparr>w_ac := ac''\<rparr>)"
  have adv_loop_bounds: "w_j (w'\<lparr>w_ac := ac''\<rparr>) = j" "w_tj (w'\<lparr>w_ac := ac''\<rparr>) = tj"
    "w_sj (w'\<lparr>w_ac := ac''\<rparr>) = sj"
    using loop unfolding matchP_loop_inv_def by auto
  have valid_w': "valid_window args t0 sub rho (w'\<lparr>w_ac := ac''\<rparr>)"
    using valid_after(9) \<beta>'_def(2)
    by (auto simp: valid_window_def Let_def)
  have adv_last_bounds: "w_i w'' = w_i (w'\<lparr>w_ac := ac''\<rparr>)" "w_ti w'' = w_ti (w'\<lparr>w_ac := ac''\<rparr>)"
    "w_si w'' = w_si (w'\<lparr>w_ac := ac''\<rparr>)" "w_j w'' = Suc (w_j (w'\<lparr>w_ac := ac''\<rparr>))"
    "w_sj w'' = sj'''" "w_tj w'' = tj'''"
    using adv_end_last adv_loop_bounds(1,2,3)
      before_end[unfolded adv_loop_bounds(2,3)[unfolded tj_def sj_def, symmetric]]
    by (auto simp: adv_end_def Let_def split: option.splits prod.splits)
  have j''_j: "w_j w'' = j + 1"
    using adv_loop_bounds adv_last_bounds by auto
  have i'_le_j: "w_i w' \<le> j"
    using valid_after(7)
    unfolding i'_def .
  have i'_set: "\<And>l. l < w_i w' \<Longrightarrow> ts_at rho' l + left I \<le> ts_at rho' j"
    using loop length_rho i'_le_j
    unfolding matchP_loop_inv_def
    by (auto simp: ts_at_def rho'_def nth_append)
  have b_alt: "(\<exists>q \<in> mmap_keys e'. t \<le> the (mmap_lookup e' q) + right I \<and>
    accept q b) \<or> (mem t t I \<and> accept {0} b) \<longleftrightarrow>
    sat j (MatchP I r)"
  proof (rule iffI, erule disjE)
    assume "\<exists>q \<in> mmap_keys e'. t \<le> the (mmap_lookup e' q) + right I \<and>
      accept q b"
    then obtain q where q_def: "q \<in> mmap_keys e'"
      "t \<le> the (mmap_lookup e' q) + right I" "accept q b"
      by auto
    then obtain ts' where ts_def: "mmap_lookup e' q = Some ts'"
      by (auto dest: Mapping_keys_dest)
    have "sup_leadsto init step rho' i' j q = Some ts'"
      using lookup_e' ts_def q_def valid_after(4,7,8)
      by (auto simp: rho'_def sup_leadsto_app_cong)
    then obtain l where l_def: "l < i'" "steps step rho' init (l, j) = q"
      "ts_at rho' l = ts'"
      using sup_leadsto_SomeE[OF i'_le_j]
      unfolding i'_def
      by fastforce
    have l_le_j: "l \<le> j"
      using l_def(1) i'_le_j by (auto simp: i'_def)
    have tau_l: "l < j \<Longrightarrow> fst (rho ! l) = \<tau> \<sigma> l"
      using run_t_sound'[OF reach_sub_tj', of l] length_rho
      by (auto simp: rho'_def nth_append)
    have tau_l_left: "ts' + left I \<le> t"
      unfolding l_def(3)[symmetric] tj_def'(2)
      using i'_set l_def(1)
      by (auto simp: i'_def)
    have "(l, j) \<in> match r"
      using accept_match[OF reach_sub_sj' l_le_j] q_def(3) length_rho init_def l_def(2)
        rho'_def
      by (auto simp: rho'_def l_def(2)[unfolded rho'_def] bs_at_def nth_append)
    then show "sat j (MatchP I r)"
      using l_le_j q_def(2) ts_at_tau[OF reach_sub_tj'] tau_l_left
      by (auto simp: mem_def tj_def' rho'_def ts_def l_def(3)[symmetric] tau_l tj_def ts_at_def
          nth_append length_rho intro: exI[of _ l] split: if_splits)
  next
    have "\<tau> \<sigma> j \<le> \<tau> \<sigma> j + right I"
      by (rule right_I_add_mono)
    then show "mem t t I \<and> accept {0} b \<Longrightarrow> sat j (MatchP I r)"
      using accept_match[OF reach_sub_sj' order.refl j_len_rho', unfolded steps_refl] bj_def
      by (auto simp add: mem_def tj_def'(1) bs_at_def nth_append)
  next
    assume "sat j (MatchP I r)"
    then obtain l where l_def: "l \<le> j" "mem (\<tau> \<sigma> l) (\<tau> \<sigma> j) I" "(l, j) \<in> match r"
      by auto
    show "(\<exists>q\<in>mmap_keys e'. t \<le> the (mmap_lookup e' q) + right I \<and>
      accept q b) \<or> mem t t I \<and> accept {0} b"
    proof (cases "l = j")
      case True
      show ?thesis
        using accept_match[OF reach_sub_sj' l_def(1) j_len_rho'] l_def(2,3) steps_refl
        unfolding True
        by (auto simp: tj_def'(1) bs_at_def nth_append bj_def)
    next
      case False
      then have l_lt_j: "l < j"
        using l_def(1) by auto
      then have ts_at_l_j: "ts_at rho' l \<le> ts_at rho' j"
        using ts_at_mono[OF reach_sub' _ j_len_rho']
        by (auto simp: rho'_def length_rho)
      have ts_j_l: "ts_at rho' l + left I \<le> ts_at rho' j"
        using l_def(2) ts_at_tau[OF reach_sub_tj'] l_lt_j length_rho tj_def'(1,2)
        unfolding rho'_def mem_def
        by auto
      have "i' = j \<or> \<not>ts_at rho' i' + left I \<le> ts_at rho' j"
      proof (rule Meson.disj_comm, rule disjCI)
        assume "i' \<noteq> j"
        then have i'_j: "i' < j"
          using valid_after
          by auto
        obtain t' b' where tbi_cur_def: "w_read_t args ti' = Some t'"
          "w_read_sub args si' = Some b'"
          "t' = ts_at rho i'" "b' = bs_at rho i'"
          using reach_window_run_ti[OF valid_after(1) i'_j]
            reach_window_run_si[OF valid_after(1) i'_j] run_t_read run_sub_read
          by auto
        show "\<not>ts_at rho' i' + left I \<le> ts_at rho' j"
          using loop tbi_cur_def(1) i'_j length_rho
          unfolding matchP_loop_inv_def matchP_loop_cond_def tj_def'(2) adv_loop_bounds
          by (auto simp: tbi_cur_def ts_at_def rho'_def nth_append i'_def)
             (metis i'_def option.sel tbi_cur_def(1) tbi_cur_def(3) ti'_def ts_at_def)
      qed
      then have l_lt_i': "l < i'"
      proof (rule disjE)
        assume assm: "\<not> ts_at rho' i' + left I \<le> ts_at rho' j"
        show "l < i'"
        proof (rule ccontr)
          assume "\<not>l < i'"
          then have ts_at_i'_l: "ts_at rho' i' \<le> ts_at rho' l"
            using ts_at_mono[OF reach_sub'] l_lt_j length_rho
            by (auto simp: rho'_def length_rho)
          show False
            using add_mono_comm[OF ts_at_i'_l, of "left I"] ts_j_l assm order_trans
            by auto
        qed
      qed (auto simp add: l_lt_j)
      define q where q_def: "q = steps step rho' init (l, j)"
      then obtain l' where l'_def: "sup_leadsto init step rho' i' j q = Some (ts_at rho' l')"
        "l \<le> l'" "l' < i'"
        using sup_leadsto_SomeI[OF l_lt_i'] by fastforce
      have ts_j_l': "ts_at rho' j \<le> ts_at rho' l' + right I"
      proof -
        have ts_at_l_l': "ts_at rho' l \<le> ts_at rho' l'"
          using ts_at_mono[OF reach_sub' l'_def(2)] l'_def(3) i'_le_j length_rho valid_after(4,7,8)
          by (auto simp add: rho'_def length_rho dual_order.order_iff_strict)
        show ?thesis
          using l_def(2) add_mono_comm[OF ts_at_l_l'] order_trans
            ts_at_tau[OF reach_sub_tj'] l'_def(2,3) i'_le_j length_rho valid_after(4,7,8)
          by (auto simp: mem_def rho'_def length_rho)
      qed
      have lookup_e'_q: "mmap_lookup e' q = Some (ts_at rho' l')"
        using lookup_e' l'_def(1) valid_after(4,7,8)
        by (auto simp: rho'_def sup_leadsto_app_cong)
      show ?thesis
        using accept_match[OF reach_sub_sj' l_def(1)] length_rho l_def(3) ts_j_l' lookup_e'_q
          q_def[unfolded rho'_def, symmetric] tj_def'(2)
        unfolding rho'_def
        by (auto simp: bs_at_def nth_append init_def intro!: bexI[of _ q]
            Mapping_keys_intro)
    qed
  qed
  define i'' where "i'' = w_i w''"
  define tj'' where "tj'' = w_tj w''"
  have rho_mono: "\<And>t'. t' \<in> set (map fst rho) \<Longrightarrow> t' \<le> t"
    using ts_at_mono[OF reach_sub', of _ "length rho"] nat_less_le
    by (fastforce simp: rho'_def ts_at_def nth_append in_set_conv_nth split: list.splits)
  have "\<And>t' l. w_read_t args tj'' = Some t' \<Longrightarrow> l < i'' \<Longrightarrow> ts_at rho' l + left I \<le> t'"
  proof -
    fix t' l
    assume lassms: "(w_read_t args) tj'' = Some t'" "l < i''"
    obtain tj'''' where reach_sub_tj'''':
      "reach_sub (w_run_t args) t0 (map fst (rho' @ [(t', undefined)])) tj''''"
      using reach_sub_app[OF reach_sub_tj'] read_t_run[OF lassms(1)]
        adv_last_bounds tj''_def
      by auto
    have "t \<le> t'"
      using ts_at_mono[OF reach_sub_tj'''', of "length rho" "length rho'"]
      by (auto simp: ts_at_def nth_append rho'_def)
    then show "ts_at rho' l + left I \<le> t'"
      using loop lassms(2) j''_j adv_last_bounds(1) i''_def i'_le_j length_rho
      unfolding adv_last_bounds matchP_loop_inv_def rho'_def
      by (auto simp: adv_last_bounds ts_at_def bs_at_def nth_append)
  qed
  moreover have "rw t0 sub rho' (w_i w'', w_ti w'', w_si w'', w_j w'', w_tj w'', w_sj w'')"
    using reach_window_app[OF valid_after(1)
        before_end[unfolded tj_def[symmetric] sj_def[symmetric]]]
    unfolding adv_last_bounds i'_def ti'_def si'_def rho'_def valid_before adv_loop_bounds
    by auto
  moreover have "valid_window args t0 sub (rho @ [(t, b)]) w''"
    using valid_adv_end[OF valid_w' before_end(1,2)[folded tj_def sj_def adv_loop_bounds] rho_mono]
    by (auto simp: adv_end_last)
  ultimately have "valid_matchP I t0 sub rho' (Suc j) (adv_end args (w'\<lparr>w_ac := ac''\<rparr>))"
    unfolding valid_window_matchP_def adv_end_last[symmetric]
    using adv_loop_bounds adv_last_bounds length_rho valid_after(6)
    by (auto simp: rho'_def i'_def i''_def tj''_def split: option.splits)
  moreover have "eval_mP I w = Some ((t, sat j (MatchP I r)), w'')"
    by (auto simp: read_t_def read_sub_def Let_def loop_def[symmetric]
        ac'_def[unfolded ac_def e'_def] ac''_def(1) adv_end_last trans[OF \<beta>'_def(1) b_alt])
  ultimately show ?thesis
    unfolding adv_end_last rho'_def tj_def'
    by auto
qed

lemma valid_eval_matchF_Some:
  assumes valid_before': "valid_matchF I t0 sub rho i w"
  and eval: "eval_mF I w = Some ((t, b), w'')"
  and bounded: "finite_ts (right I)"
  shows "\<exists>rho' t tm. reach_sub (w_run_t args) (w_tj w) (map fst rho') (w_tj w'') \<and>
    reach_sub (w_run_sub args) (w_sj w) (map snd rho') (w_sj w'') \<and>
    (w_read_t args) (w_ti w) = Some t \<and>
    (w_read_t args) (w_tj w'') = Some tm \<and>
    \<not>tm \<le> t + right I"
proof -
  define st where "st = w_st w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "rw t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    "valid_s init step st accept rho i i j s"
    "i = w_i w" "i \<le> j" "length rho = j"
    using valid_before'[unfolded valid_window_matchF_def] ti_def
      si_def j_def tj_def sj_def s_def e_def
    by (auto simp: valid_window_def Let_def init_def step_def st_def accept_def)
  obtain ti''' t where tbi_def: "w_run_t args ti = Some (ti''', t)"
    using eval read_t_run read_sub_run
    by (fastforce simp: Let_def ti_def si_def split: option.splits if_splits)
  have t_tau: "t = \<tau> \<sigma> i"
    using run_t_sound[OF _ tbi_def] valid_before(1)
    by auto (metis (full_types) min_less_iff_conj nat_less_le nat_neq_iff)
  note t_def = run_t_read[OF tbi_def(1)]
  define w' where loop_def: "w' = while (matchF_cond I t) (adv_end args) w"
  have adv_start_last:
    "adv_start args w' = w''"
    using eval loop_def[symmetric] run_t_read[OF tbi_def(1)]
    by (auto simp: ti_def split: option.splits prod.splits if_splits)
  have inv_before: "matchF_inv' t0 sub rho i ti si j tj sj w"
    using valid_before(1) valid_before'
    unfolding matchF_loop_inv'_def valid_before(6) valid_window_matchF_def
    by (auto simp add: ti_def si_def j_def tj_def sj_def simp del: reach_window.simps
        dest: reach_window_shift_all intro!: exI[of _ "[]"])
  have i_j: "i \<le> j" "length rho = j"
    using valid_before by auto
  define j'' where "j'' = w_j w''"
  define tj'' where "tj'' = w_tj w''"
  define sj'' where "sj'' = w_sj w''"
  have loop: "matchF_inv' t0 sub rho i ti si j tj sj w' \<and> \<not> matchF_cond I t w'"
    unfolding loop_def
  proof (rule while_rule_lemma[of "matchF_inv' t0 sub rho i ti si j tj sj"])
    fix w_cur :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchF_inv' t0 sub rho i ti si j tj sj w_cur" "matchF_cond I t w_cur"
    define j_cur where "j_cur = w_j w_cur"
    define tj_cur where "tj_cur = w_tj w_cur"
    define sj_cur where "sj_cur = w_sj w_cur"
    obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w_cur"
      "rw t0 sub (rho @ rho') (j, tj, sj, w_j w_cur, w_tj w_cur, w_sj w_cur)"
      using assms(1)[unfolded matchF_loop_inv'_def valid_window_matchF_def]
      by auto
    obtain tj' x sj' y where append: "w_run_t args tj_cur = Some (tj', x)"
      "w_run_sub args sj_cur = Some (sj', y)"
      using assms[unfolded matchF_loop_cond_def] read_t_run read_sub_run
      unfolding tj_cur_def sj_cur_def
      by (fastforce split: option.splits)
    note append' = append[unfolded tj_cur_def sj_cur_def]
    define rho'' where "rho'' = rho @ rho'"
    have reach: "reach_sub (w_run_t args) t0 (map fst (rho'' @ [(x, undefined)])) tj'"
      using reach_sub_app[OF reach_window_run_tj[OF rho'_def(2)] append'(1)]
      by (auto simp: rho''_def)
    have mono: "\<And>t'. t' \<in> set (map fst rho'') \<Longrightarrow> t' \<le> x"
      using ts_at_mono[OF reach, of _ "length rho''"] nat_less_le
      by (fastforce simp: ts_at_def nth_append in_set_conv_nth split: list.splits)
    show "matchF_inv' t0 sub rho i ti si j tj sj (adv_end args w_cur)"
      using assms(1) reach_window_app[OF rho'_def(2) append[unfolded tj_cur_def sj_cur_def]]
        valid_adv_end[OF rho'_def(1) append' mono] adv_end_bounds[OF append']
      unfolding matchF_loop_inv'_def matchF_loop_cond_def rho''_def
      by auto
  next
    obtain l where l_def: "\<not>\<tau> \<sigma> l \<le> t + right I"
      unfolding t_tau
      using ex_lt_\<tau>[OF bounded]
      by auto
    {
      fix w1 w2
      assume lassms: "matchF_inv' t0 sub rho i ti si j tj sj w1" "matchF_cond I t w1"
        "w2 = adv_end args w1"
      define j_cur where "j_cur = w_j w1"
      define tj_cur where "tj_cur = w_tj w1"
      define sj_cur where "sj_cur = w_sj w1"
      obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w1"
        "rw t0 sub (rho @ rho') (j, tj, sj, w_j w1, w_tj w1, w_sj w1)"
        using lassms(1)[unfolded matchF_loop_inv'_def valid_window_matchF_def]
        by auto
      obtain tj' x sj' y where append: "w_run_t args tj_cur = Some (tj', x)"
        "w_run_sub args sj_cur = Some (sj', y)"
        using lassms[unfolded matchF_loop_cond_def] read_t_run read_sub_run
        unfolding tj_cur_def sj_cur_def
        by (fastforce split: option.splits)
      note append' = append[unfolded tj_cur_def sj_cur_def]
      define rho'' where "rho'' = rho @ rho'"
      have reach: "reach_sub (w_run_t args) t0 (map fst (rho'' @ [(x, undefined)])) tj'"
        using reach_sub_app[OF reach_window_run_tj[OF rho'_def(2)] append'(1)]
        by (auto simp: rho''_def)
      have mono: "\<And>t'. t' \<in> set (map fst rho'') \<Longrightarrow> t' \<le> x"
        using ts_at_mono[OF reach, of _ "length rho''"] nat_less_le
        by (fastforce simp: ts_at_def nth_append in_set_conv_nth split: list.splits)
      have t_cur_tau: "x = \<tau> \<sigma> j_cur"
        using ts_at_tau[OF reach, of "length rho''"] rho'_def(2)
        by (auto simp: ts_at_def j_cur_def rho''_def)
      have "j_cur < l"
        using lassms(2)[unfolded matchF_loop_cond_def]
          l_def \<tau>_mono[of l j_cur \<sigma>]
        unfolding run_t_read[OF append(1), unfolded t_cur_tau tj_cur_def]
        by (metis leI option.simps(5) order.trans)
      moreover have "w_j w2 = Suc j_cur"
        using adv_end_bounds[OF append']
        unfolding lassms(3) j_cur_def
        by auto
      ultimately have "l - w_j w2 < l - w_j w1"
        unfolding j_cur_def
        by auto
    }
    then have "{(ta, s). matchF_inv' t0 sub rho i ti si j tj sj s \<and> matchF_cond I t s \<and>
      ta = adv_end args s} \<subseteq> measure (\<lambda>w. l - w_j w)"
      by auto
    then show "wf {(ta, s). matchF_inv' t0 sub rho i ti si j tj sj s \<and> matchF_cond I t s \<and>
      ta = adv_end args s}"
      using wf_measure wf_subset
      by auto
  qed (auto simp: inv_before)
  define i' where "i' = w_i w'"
  define ti' where "ti' = w_ti w'"
  define si' where "si' = w_si w'"
  define j' where "j' = w_j w'"
  define tj' where "tj' = w_tj w'"
  define sj' where "sj' = w_sj w'"
  obtain rho' where rho'_def: "valid_window args t0 sub (rho @ rho') w'"
    "rw t0 sub (rho @ rho') (j, tj, sj, j', tj', sj')"
    "i = i'" "j \<le> j'"
    using loop
    unfolding matchF_loop_inv'_def i'_def j'_def tj'_def sj'_def
    by auto
  obtain tje tm where tm_def: "w_read_t args tj' = Some tm" "w_run_t args tj' = Some (tje, tm)"
    using eval read_t_run loop_def t_def ti_def
    by (auto simp: t_def Let_def tj'_def split: option.splits if_splits)
  have drop_j_rho: "drop j (map fst (rho @ rho')) = map fst rho'"
    using i_j
    by auto
  have "reach_sub (w_run_t args) ti (drop i (map fst rho)) tj"
    using valid_before(1)
    by auto
  then have "reach_sub (w_run_t args) ti
    (drop i (map fst rho) @ (drop j (map fst (rho @ rho')))) tj'"
    using rho'_def reach_sub_trans
    by fastforce
  then have "reach_sub (w_run_t args) ti (drop i (map fst (rho @ rho'))) tj'"
    unfolding drop_j_rho
    by (auto simp: i_j)
  then have reach_tm: "reach_sub (w_run_t args) ti (drop i (map fst (rho @ rho')) @ [tm]) tje"
    using reach_sub_app tm_def(2)
    by fastforce
  have run_tsi': "w_run_t args ti' \<noteq> None"
    using tbi_def loop
    by (auto simp: matchF_loop_inv'_def ti'_def si'_def)
  have not_ets_tm: "\<not> tm \<le> t + right I"
    using eval run_tsi' loop_def t_def tm_def
    by (auto simp: ti_def ti'_def si'_def tj'_def split: option.splits)
  have i_le_rho: "i \<le> length rho"
    using valid_before
    by auto
  define rho'' where "rho'' = rho @ rho'"
  have i'_lt_j': "i' < j'"
    using rho'_def(1,2,3)[folded rho''_def] i_j reach_tm[folded rho''_def] not_ets_tm tbi_def
      right_I_add_mono
    by (cases "i' = j'") (auto dest!: reach_sub_NilD elim!: reach_sub.cases[of _ _ "[tm]"])+
  have adv_last_bounds: "j'' = j'" "tj'' = tj'" "sj'' = sj'"
    using valid_adv_start_bounds[OF rho'_def(1) i'_lt_j'[unfolded i'_def j'_def]]
    unfolding adv_start_last j'_def j''_def tj'_def tj''_def sj'_def sj''_def
    by auto
  show ?thesis
    using eval rho'_def run_tsi' i_j(2) not_ets_tm adv_last_bounds tj''_def tj_def sj''_def sj_def
      loop_def t_def ti_def tj'_def
    by (auto simp: tm_def drop_map run_t_read[OF tbi_def(1)] Let_def
        split: option.splits prod.splits if_splits intro!: exI[of _ rho'])
qed

lemma valid_eval_matchF_complete:
  assumes valid_before': "valid_matchF I t0 sub rho i w"
    and before_end: "reach_sub (w_run_t args) (w_tj w) (map fst rho') tj'''"
    "reach_sub (w_run_sub args) (w_sj w) (map snd rho') sj'''"
    "w_read_t args (w_ti w) = Some t" "w_read_t args tj''' = Some tm" "\<not>tm \<le> t + right I"
  shows "\<exists>w'. eval_mF I w = Some ((\<tau> \<sigma> i, sat i (MatchF I r)), w') \<and>
    valid_matchF I t0 sub (take (w_j w') (rho @ rho')) (Suc i) w'"
proof -
  define st where "st = w_st w"
  define ti where "ti = w_ti w"
  define si where "si = w_si w"
  define j where "j = w_j w"
  define tj where "tj = w_tj w"
  define sj where "sj = w_sj w"
  define s where "s = w_s w"
  define e where "e = w_e w"
  have valid_before: "rw t0 sub rho (i, ti, si, j, tj, sj)"
    "\<And>i j. i \<le> j \<Longrightarrow> j < length rho \<Longrightarrow> ts_at rho i \<le> ts_at rho j"
    "\<forall>q. mmap_lookup e q = sup_leadsto init step rho i j q"
    "valid_s init step st accept rho i i j s"
    "i = w_i w" "i \<le> j" "length rho = j"
    using valid_before'[unfolded valid_window_matchF_def] ti_def
      si_def j_def tj_def sj_def s_def e_def
    by (auto simp: valid_window_def Let_def init_def step_def st_def accept_def)
  define rho'' where "rho'' = rho @ rho'"
  have ij_le: "i \<le> j" "j = length rho"
    using valid_before
    by auto
  have reach_tj: "reach_sub (w_run_t args) t0 (take j (map fst rho'')) tj"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def simp del: reach_window.simps dest!: reach_window_run_tj)
  have reach_ti: "reach_sub (w_run_t args) t0 (take i (map fst rho'')) ti"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def)
  have reach_si: "reach_sub (w_run_sub args) sub (take i (map snd rho'')) si"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def)
  have reach_sj: "reach_sub (w_run_sub args) sub (take j (map snd rho'')) sj"
    using valid_before(1) ij_le
    by (auto simp: take_map rho''_def simp del: reach_window.simps dest!: reach_window_run_sj)
  have reach_tj''': "reach_sub (w_run_t args) t0 (map fst rho'') tj'''"
    using reach_sub_trans[OF reach_tj before_end(1)[folded tj_def]] ij_le(2)
    by (auto simp del: map_append simp: rho''_def take_map drop_map map_append[symmetric])
  have rho''_mono: "\<And>i j. i \<le> j \<Longrightarrow> j < length rho'' \<Longrightarrow> ts_at rho'' i \<le> ts_at rho'' j"
    using ts_at_mono[OF reach_tj'''] .
  obtain tm' where reach_tm: "reach_sub (w_run_t args) t0
    (map fst (rho'' @ [(tm, undefined)])) tm'"
    using reach_sub_app[OF reach_tj'''] read_t_run[OF before_end(4)]
    by auto
  have tj'''_eq: "\<And>tj_cur. reach_sub (w_run_t args) t0 (map fst rho'') tj_cur \<Longrightarrow>
    tj_cur = tj'''"
    using reach_sub_inj[OF reach_tj''']
    by blast
  have reach_sj''': "reach_sub (w_run_sub args) sub (map snd rho'') sj'''"
    using reach_sub_trans[OF reach_sj before_end(2)[folded sj_def]] ij_le(2)
    by (auto simp del: map_append simp: rho''_def take_map drop_map map_append[symmetric])
  have sj'''_eq: "\<And>sj_cur. reach_sub (w_run_sub args) sub (map snd rho'') sj_cur \<Longrightarrow>
    sj_cur = sj'''"
    using reach_sub_inj[OF reach_sj''']
    by blast
  have reach_window_i: "rw t0 sub rho'' (i, ti, si, length rho'', tj''', sj''')"
    using reach_windowI[OF reach_ti reach_si reach_tj''' reach_sj''' _ refl] ij_le
    by (auto simp: rho''_def)
  have reach_window_j: "rw t0 sub rho'' (j, tj, sj, length rho'', tj''', sj''')"
    using reach_windowI[OF reach_tj reach_sj reach_tj''' reach_sj''' _ refl] ij_le
    by (auto simp: rho''_def)
  have i_lt_rho'': "i < length rho''"
    using ij_le before_end(3,4,5) reach_window_i
    by (cases "i = length rho''")
       (auto simp: rho''_def ti_def right_I_add_mono dest!: reach_sub_NilD)
  obtain ti''' si''' b where tbi_def: "w_run_t args ti = Some (ti''', t)"
    "w_run_sub args si = Some (si''', b)" "t = ts_at rho'' i" "b = bs_at rho'' i"
    using reach_window_run_ti[OF reach_window_i i_lt_rho'']
      reach_window_run_si[OF reach_window_i i_lt_rho'']
      read_t_run[OF before_end(3), folded ti_def]
    by auto
  have t_def: "t = \<tau> \<sigma> i"
    using tbi_def(3) ts_at_tau[OF reach_tj''' i_lt_rho'']
    by auto
  note before_end' = before_end(5)
  have read_ti: "w_read_t args ti = Some t"
    using run_t_read[OF tbi_def(1)] .
  have read_si: "w_read_sub args si = Some b"
    using run_sub_read[OF tbi_def(2)] .
  define w' where loop_def: "w' = while (matchF_cond I t) (adv_end args) w"
  define w'' where adv_start_last: "w'' = adv_start args w'"
  have inv_before: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w"
    using valid_before' before_end(1,2,3) reach_window_j ij_le ti_def si_def j_def tj_def sj_def
    unfolding matchF_loop_inv_def valid_window_matchF_def
    by (auto simp: rho''_def ts_at_def nth_append)
  have i_j: "i \<le> j"
    using valid_before by auto
  have loop: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w' \<and> \<not> matchF_cond I t w'"
    unfolding loop_def
  proof (rule while_rule_lemma[of "matchF_inv I t0 sub rho'' i ti si tj''' sj'''"])
    fix w_cur :: "(bool iarray, nat set, 'd, 't, 'e) window"
    assume assms: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w_cur" "matchF_cond I t w_cur"
    define j_cur where "j_cur = w_j w_cur"
    define tj_cur where "tj_cur = w_tj w_cur"
    define sj_cur where "sj_cur = w_sj w_cur"
    define s_cur where "s_cur = w_s w_cur"
    define e_cur where "e_cur = w_e w_cur"
    have loop: "valid_window args t0 sub (take (w_j w_cur) rho'') w_cur"
      "rw t0 sub rho'' (j_cur, tj_cur, sj_cur, length rho'', tj''', sj''')"
      "\<And>l. l\<in>{w_i w_cur..<w_j w_cur} \<Longrightarrow> ts_at rho'' l \<le> ts_at rho'' i + right I"
      using j_cur_def tj_cur_def sj_cur_def s_cur_def e_cur_def
        assms(1)[unfolded matchF_loop_inv_def]
      by auto
    have j_cur_lt_rho'': "j_cur < length rho''"
      using assms tj'''_eq ij_le before_end(4,5) right_I_add_mono
      unfolding matchF_loop_inv_def matchF_loop_cond_def
      by (cases "j_cur = length rho''") (auto simp: j_cur_def split: option.splits)
    obtain tj_cur' sj_cur' x b_cur where tbi_cur_def: "w_run_t args tj_cur = Some (tj_cur', x)"
      "w_run_sub args sj_cur = Some (sj_cur', b_cur)"
      "x = ts_at rho'' j_cur" "b_cur = bs_at rho'' j_cur"
      using reach_window_run_ti[OF loop(2) j_cur_lt_rho'']
        reach_window_run_si[OF loop(2) j_cur_lt_rho'']
      by auto
    note reach_window_j'_cur = reach_window_shift[OF loop(2) j_cur_lt_rho'' tbi_cur_def(1,2)]
    note tbi_cur_def' = tbi_cur_def(1,2)[unfolded tj_cur_def sj_cur_def]
    have mono: "\<And>t'. t' \<in> set (map fst (take (w_j w_cur) rho'')) \<Longrightarrow> t' \<le> x"
      using rho''_mono[of _ j_cur] j_cur_lt_rho'' nat_less_le
      by (fastforce simp: tbi_cur_def(3) j_cur_def ts_at_def nth_append in_set_conv_nth
          split: list.splits)
    have take_unfold: "take (w_j w_cur) rho'' @ [(x, b_cur)] = (take (Suc (w_j w_cur)) rho'')"
      using j_cur_lt_rho''
      unfolding tbi_cur_def(3,4)
      by (auto simp: ts_at_def bs_at_def j_cur_def take_Suc_conv_app_nth)
    have "\<And>l. l \<in>{w_i (adv_end args w_cur)..<w_j (adv_end args w_cur)} \<Longrightarrow>
      ts_at rho'' l \<le> ts_at rho'' i + right I"
      using loop(3) assms(2)
      unfolding adv_end_bounds[OF tbi_cur_def'] matchF_loop_cond_def
        run_t_read[OF tbi_cur_def(1)[unfolded tj_cur_def]] tbi_cur_def(3) tbi_def(3)
      by (auto simp: j_cur_def elim: less_SucE)
    then show "matchF_inv I t0 sub rho'' i ti si tj''' sj''' (adv_end args w_cur)"
      using assms(1) reach_window_j'_cur
        valid_adv_end[OF loop(1) tbi_cur_def' mono]
      unfolding matchF_loop_inv_def ti_def si_def j_cur_def valid_window_matchF_def take_unfold
        adv_end_bounds[OF tbi_cur_def']
      by auto
  next
    {
      fix w1 w2
      assume lassms: "matchF_inv I t0 sub rho'' i ti si tj''' sj''' w1" "matchF_cond I t w1"
        "w2 = adv_end args w1"
      define j_cur where "j_cur = w_j w1"
      define tj_cur where "tj_cur = w_tj w1"
      define sj_cur where "sj_cur = w_sj w1"
      define s_cur where "s_cur = w_s w1"
      define e_cur where "e_cur = w_e w1"
      have loop: "valid_window args t0 sub (take (w_j w1) rho'') w1"
        "rw t0 sub rho'' (j_cur, tj_cur, sj_cur, length rho'', tj''', sj''')"
        "\<And>l. l\<in>{w_i w1..<w_j w1} \<Longrightarrow> ts_at rho'' l \<le> ts_at rho'' i + right I"
        using j_cur_def tj_cur_def sj_cur_def s_cur_def e_cur_def
          lassms(1)[unfolded matchF_loop_inv_def]
        by auto
      have j_cur_lt_rho'': "j_cur < length rho''"
        using lassms tj'''_eq ij_le before_end(4,5) right_I_add_mono
        unfolding matchF_loop_inv_def matchF_loop_cond_def
        by (cases "j_cur = length rho''") (auto simp: j_cur_def split: option.splits)
      obtain tj_cur' sj_cur' x b_cur where tbi_cur_def: "w_run_t args tj_cur = Some (tj_cur', x)"
        "w_run_sub args sj_cur = Some (sj_cur', b_cur)"
        "x = ts_at rho'' j_cur" "b_cur = bs_at rho'' j_cur"
        using reach_window_run_ti[OF loop(2) j_cur_lt_rho'']
          reach_window_run_si[OF loop(2) j_cur_lt_rho'']
        by auto
      note tbi_cur_def' = tbi_cur_def(1,2)[unfolded tj_cur_def sj_cur_def]
      have "length rho'' - w_j w2 < length rho'' - w_j w1"
        using j_cur_lt_rho'' adv_end_bounds[OF tbi_cur_def', folded lassms(3)]
        unfolding j_cur_def
        by auto
    }
    then have "{(ta, s). matchF_inv I t0 sub rho'' i ti si tj''' sj''' s \<and> matchF_cond I t s \<and>
      ta = adv_end args s} \<subseteq> measure (\<lambda>w. length rho'' - w_j w)"
      by auto
    then show "wf {(ta, s). matchF_inv I t0 sub rho'' i ti si tj''' sj''' s \<and> matchF_cond I t s \<and>
      ta = adv_end args s}"
      using wf_measure wf_subset
      by auto
  qed (auto simp add: inv_before)
  define st' where "st' = w_st w'"
  define i' where "i' = w_i w'"
  define ti' where "ti' = w_ti w'"
  define si' where "si' = w_si w'"
  define j' where "j' = w_j w'"
  define tj' where "tj' = w_tj w'"
  define sj' where "sj' = w_sj w'"
  define s' where "s' = w_s w'"
  define e' where "e' = w_e w'"
  have valid_after: "valid_window args t0 sub (take (w_j w') rho'') w'"
    "rw t0 sub rho'' (j', tj', sj', length rho'', tj''', sj''')"
    "\<And>l. l\<in>{i..<j'} \<Longrightarrow> ts_at rho'' l \<le> ts_at rho'' i + right I"
    "i' = i" "ti' = ti" "si' = si"
    using loop
    unfolding matchF_loop_inv_def i'_def ti'_def si'_def j'_def tj'_def sj'_def
    by auto
  define i'' where "i'' = w_i w''"
  define j'' where "j'' = w_j w''"
  define tj'' where "tj'' = w_tj w''"
  define sj'' where "sj'' = w_sj w''"
  have j'_le_rho'': "j' \<le> length rho''"
    using loop
    unfolding matchF_loop_inv_def valid_window_matchF_def j'_def
    by auto
  obtain te where tbj'_def: "w_read_t args tj' = Some te"
    "te = ts_at (rho'' @ [(tm, undefined)]) j'"
    subgoal premises prems
    proof (cases "j' < length rho''")
      case True
      show ?thesis
        using reach_window_run_ti[OF valid_after(2) True] prems True
        by (auto simp: ts_at_def nth_append dest!: run_t_read)
    next
      case False
      then have "tj' = tj'''" "j' = length rho''"
        using valid_after(2) j'_le_rho'' tj'''_eq
        by auto
      then show ?thesis
        using prems before_end(4)
        by (auto simp: ts_at_def nth_append)
    qed
    done
  have not_ets_te: "\<not>te \<le> ts_at rho'' i + right I"
  proof (rule ccontr)
    assume "\<not>\<not>te \<le> ts_at rho'' i + right I"
    then have contr: "te \<le> ts_at rho'' i + right I"
      by simp
    then have run_sj': "w_run_sub args sj' = None"
      using loop run_sub_read[of sj'] tbj'_def(1)
      unfolding matchF_loop_cond_def
      by (cases "w_run_sub args sj'") (auto simp:  tbi_def(3) tj'_def sj'_def split: option.splits)
    then have "j' = length rho''"
      using sj'''_eq reach_window_run_si[OF valid_after(2)] j'_le_rho''
      by (cases "j' = length rho''") auto
    then show "False"
      using tbj'_def(2) before_end(5) contr i_lt_rho'' tbi_def(3)
      by (auto simp: rho''_def ts_at_def nth_append split: if_splits)
  qed
  have i'_set: "\<And>l. l \<in> {i..<j'} \<Longrightarrow> ts_at rho'' l \<le> ts_at rho'' i + right I"
    "\<not>ts_at (rho'' @ [(tm, undefined)]) j' \<le> ts_at rho'' i + right I"
    using loop tbj'_def not_ets_te
    unfolding matchF_loop_inv_def matchF_loop_cond_def tbi_def(3)
     apply (auto simp: tbi_def tj'_def split: option.splits)
    using valid_after atLeastLessThan_iff i'_def j'_def by blast
  have i_le_j': "i \<le> j'"
    using valid_after(1)
    unfolding valid_after(4)[symmetric]
    by (auto simp: valid_window_def Let_def i'_def j'_def)
  have i_lt_j': "i < j'"
    using i_le_j' i'_set(2) right_I_add_mono[of "ts_at (rho'' @ [(tm, undefined)]) j'" I]
      i_lt_rho''
    by (cases "i = j'") (auto simp: ts_at_def nth_append)
  then have i'_lt_j': "i' < j'"
    unfolding valid_after
    by auto
  have adv_last_bounds: "i'' = Suc i'" "w_ti w'' = ti'''" "w_si w'' = si'''" "j'' = j'"
    "tj'' = tj'" "sj'' = sj'"
    using valid_adv_start_bounds[OF valid_after(1) i'_lt_j'[unfolded i'_def j'_def]]
      valid_adv_start_bounds'[OF valid_after(1) tbi_def(1,2)[folded valid_after(5,6),
      unfolded ti'_def si'_def]]
    unfolding adv_start_last i'_def i''_def j'_def j''_def tj'_def tj''_def sj'_def sj''_def
    by auto
  have i''_i: "i'' = i + 1"
    using valid_after adv_last_bounds by auto
  have i_le_j': "i \<le> j'"
    using valid_after i'_lt_j'
    by auto
  then have i_le_rho: "i \<le> length rho''"
    using valid_after(2)
    by auto
  have "valid_s init step st' accept (take j' rho'') i i j' s'"
    using valid_after(1,4) i'_def
    by (auto simp: valid_window_def Let_def init_def step_def st'_def accept_def j'_def s'_def)
  note valid_s' = this[unfolded valid_s_def]
  have q0_in_keys: "{0} \<in> mmap_keys s'"
    using valid_s' init_def steps_refl by auto
  then obtain q' tstp where lookup_s': "mmap_lookup s' {0} = Some (q', tstp)"
    by (auto dest: Mapping_keys_dest)
  have lookup_sup_acc: "snd (the (mmap_lookup s' {0})) =
    sup_acc step accept (take j' rho'') {0} i j'"
    using conjunct2[OF valid_s'] lookup_s'
    by auto (smt case_prodD option.simps(5))
  have b_alt: "(case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
    | Some tstp \<Rightarrow> t + left I \<le> fst tstp) \<longleftrightarrow> sat i (MatchF I r)"
  proof (rule iffI)
    assume assm: "case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
      | Some tstp \<Rightarrow> t + left I \<le> fst tstp"
    then obtain ts tp where tstp_def:
      "sup_acc step accept (take j' rho'') {0} i j' = Some (ts, tp)"
      "ts_at rho'' i + left I \<le> ts"
      unfolding lookup_sup_acc
      by (auto simp: tbi_def split: option.splits)
    then have sup_acc_rho'': "sup_acc step accept rho'' {0} i j' = Some (ts, tp)"
      using sup_acc_concat_cong[of j' "take j' rho''" step accept "drop j' rho''"] j'_le_rho''
      by auto
    have tp_props: "tp \<in> {i..<j'}" "acc step accept rho'' {0} (i, tp)"
      using sup_acc_SomeE[OF sup_acc_rho''] by auto
    have ts_ts_at: "ts = ts_at rho'' tp"
      using sup_acc_Some_ts[OF sup_acc_rho''] .
    have i_le_tp: "i \<le> tp"
      using tp_props by auto
    have "ts_at rho'' tp \<le> ts_at rho'' i + right I"
      using i'_set(1)[OF tp_props(1)] .
    then have "mem (ts_at rho'' i) (ts_at rho'' tp) I"
      using tstp_def(2) unfolding ts_ts_at mem_def by auto
    then show "sat i (MatchF I r)"
      using i_le_tp acc_match[OF reach_sj''' i_le_tp] tp_props(2) ts_at_tau[OF reach_tj''']
        tp_props(1) j'_le_rho''
      by auto
  next
    assume "sat i (MatchF I r)"
    then obtain l where l_def: "l \<ge> i" "mem (\<tau> \<sigma> i) (\<tau> \<sigma> l) I" "(i, l) \<in> match r"
      by auto
    have l_lt_rho: "l < length rho''"
    proof (rule ccontr)
      assume contr: "\<not>l < length rho''"
      have "tm = ts_at (rho'' @ [(tm, undefined)]) (length rho'')"
        using i_le_rho
        by (auto simp add: ts_at_def rho''_def)
      moreover have "\<dots> \<le> \<tau> \<sigma> l"
        using \<tau>_mono ts_at_tau[OF reach_tm] i_le_rho contr
        by (metis One_nat_def Suc_eq_plus1 length_append lessI list.size(3)
            list.size(4) not_le_imp_less)
      moreover have "\<tau> \<sigma> l \<le> \<tau> \<sigma> i + right I"
        using l_def(2)
        unfolding mem_def
        by auto
      ultimately have "tm \<le> \<tau> \<sigma> i + right I"
        by auto
      then show "False"
        using before_end' ts_at_tau[OF reach_tj''' i_lt_rho''] tbi_def(3)
        by (auto simp: rho''_def)
    qed
    have l_lt_j': "l < j'"
    proof (rule ccontr)
      assume contr: "\<not>l < j'"
      then have ts_at_j'_l: "ts_at rho'' j' \<le> ts_at rho'' l"
        using ts_at_mono[OF reach_tj'''] l_lt_rho
        by (auto simp add: order.not_eq_order_implies_strict)
      have ts_at_l_iu: "ts_at rho'' l \<le> ts_at rho'' i + right I"
        using l_def(2) ts_at_tau[OF reach_tj''' l_lt_rho] ts_at_tau[OF reach_tj''' i_lt_rho'']
        unfolding mem_def
        by auto
      show "False"
        using i'_set(2) order_trans ts_at_j'_l ts_at_l_iu contr l_lt_rho
        by (auto simp: ts_at_def nth_append split: if_splits)
    qed
    obtain tp where tstp_def: "sup_acc step accept rho'' {0} i j' = Some (ts_at rho'' tp, tp)"
      "l \<le> tp" "tp < j'"
      using sup_acc_SomeI[unfolded acc_is_accept, of step accept] l_def(1,3) l_lt_j' l_lt_rho
      by auto (meson accept_match[OF reach_sj''' l_def(1), unfolded steps_is_run] acc_is_accept
          atLeastLessThan_iff sup_acc_SomeI)
    have "ts_at rho'' i + left I \<le> ts_at rho'' l"
      using l_def(2)
      unfolding ts_at_tau[OF reach_tj''' i_lt_rho'', symmetric]
        ts_at_tau[OF reach_tj''' l_lt_rho, symmetric] mem_def
      by auto
    then have "ts_at rho'' i + left I \<le> ts_at rho'' tp"
      using ts_at_mono[OF reach_tj''' tstp_def(2)] tstp_def(3) j'_le_rho''
      by auto
    then show "case snd (the (mmap_lookup s' {0})) of None \<Rightarrow> False
      | Some tstp \<Rightarrow> t + left I \<le> fst tstp"
      using lookup_sup_acc tstp_def j'_le_rho''
        sup_acc_concat_cong[of j' "take j' rho''" step accept "drop j' rho''"]
      by (auto simp: tbi_def split: option.splits)
  qed
  have "valid_matchF I t0 sub (take j'' rho'') i'' (adv_start args w')"
  proof -
    have "\<forall>l \<in> {i'..<j'}. ts_at rho'' l \<le> ts_at rho'' i' + right I"
      using loop i'_def j'_def valid_after
      unfolding matchF_loop_inv_def
      by auto
    moreover have "Suc i < j' \<Longrightarrow> ts_at rho'' i + right I \<le> ts_at rho'' (Suc i) + right I"
    proof -
      assume lassm: "Suc i < j'"
      have "ts_at rho'' i + right I = right I + ts_at rho'' i"
        by (auto simp add: add.commute)
      moreover have "\<dots> \<le> right I + ts_at rho'' (Suc i)"
        using add_mono ts_at_mono[OF reach_tj''', of i "Suc i"] lassm j'_le_rho''
        by auto
      moreover have "\<dots> = ts_at rho'' (Suc i) + right I"
        by (auto simp add: add.commute)
      ultimately show ?thesis
        by auto
    qed
    ultimately have "\<forall>l \<in> {i''..<j''}. ts_at rho'' l \<le> ts_at rho'' i'' + right I"
      unfolding i''_i valid_after adv_last_bounds
      apply auto
      subgoal for l
        apply (drule ballE[of _ _ l])
        apply auto
        done
      done
    moreover have "rw t0 sub (take j'' rho'') (i'', ti''', si''', j'', tj'', sj'')"
    proof -
      have rw: "rw t0 sub (take j' rho'') (i', ti', si', j', tj', sj')"
        using valid_after(1)
        by (auto simp: valid_window_def Let_def i'_def ti'_def si'_def j'_def tj'_def sj'_def)
      show ?thesis
        using reach_window_shift[OF rw i'_lt_j'
            tbi_def(1,2)[unfolded valid_after(5,6)[symmetric]]] adv_last_bounds
        by auto
    qed
    moreover have "valid_window args t0 sub (take j' rho'') w''"
      using valid_adv_start[OF valid_after(1) i'_lt_j'[unfolded i'_def j'_def]]
      unfolding adv_start_last j'_def .
    ultimately show "valid_matchF I t0 sub (take j'' rho'') i'' (adv_start args w')"
      using j'_le_rho''
      unfolding valid_window_matchF_def adv_last_bounds adv_start_last[symmetric] i''_def[symmetric]
        j'_def j''_def[symmetric] tj'_def tj''_def[symmetric] sj'_def sj''_def[symmetric]
      by (auto simp: ts_at_def)
  qed
  moreover have "eval_mF I w = Some ((\<tau> \<sigma> i, sat i (MatchF I r)), w'')"
    unfolding j''_def adv_start_last[symmetric] adv_last_bounds valid_after rho''_def
      eval_matchF.simps run_t_read[OF tbi_def(1)[unfolded ti_def]]
      run_sub_read[OF tbi_def(2)[unfolded si_def]]
    using loop_def tbj'_def[unfolded tj'_def] not_ets_te[folded tbi_def(3)]
      b_alt[unfolded s'_def] t_def adv_start_last
    by (auto simp only: Let_def split: option.splits if_splits)
  ultimately show ?thesis
    unfolding j''_def adv_start_last[symmetric] adv_last_bounds valid_after rho''_def
    by auto
qed

lemma valid_eval_matchF_sound:
  assumes valid_before: "valid_matchF I t0 sub rho i w"
  and eval: "eval_mF I w = Some ((t, b), w'')"
  and bounded: "finite_ts (right I)"
shows "t = \<tau> \<sigma> i \<and> b = sat i (MatchF I r) \<and> (\<exists>rho'. valid_matchF I t0 sub rho' (Suc i) w'')"
proof -
  obtain rho' t tm where rho'_def: "reach_sub (w_run_t args) (w_tj w) (map fst rho') (w_tj w'')"
    "reach_sub (w_run_sub args) (w_sj w) (map snd rho') (w_sj w'')"
    "w_read_t args (w_ti w) = Some t"
    "w_read_t args (w_tj w'') = Some tm"
    "\<not>tm \<le> t + right I"
    using valid_eval_matchF_Some[OF assms]
    by auto
  show ?thesis
    using valid_eval_matchF_complete[OF assms(1) rho'_def]
    unfolding eval
    by blast
qed

thm valid_eval_matchP
thm valid_eval_matchF_sound
thm valid_eval_matchF_complete

end

end