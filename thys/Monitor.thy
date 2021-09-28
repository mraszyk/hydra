theory Monitor
  imports MDL Temporal
begin

type_synonym ('e, 'd) time = "('e \<times> 'd) option"

datatype (dead 'a, dead 'd :: timestamp, dead 'e) vydra_rec =
  VYDRA_Bool bool 'e
  | VYDRA_Atom 'a 'e
  | VYDRA_Neg "('a, 'd, 'e) vydra"
  | VYDRA_Bin "bool \<Rightarrow> bool \<Rightarrow> bool" "('a, 'd, 'e) vydra" "('a, 'd, 'e) vydra"
  | VYDRA_MatchP "'d \<I>" "transition iarray" nat
    "(bool iarray, nat set, 'd, ('e, 'd) time, ('a, 'd, 'e) vydra list) window"
  | VYDRA_MatchF "'d \<I>" "transition iarray" nat
    "(bool iarray, nat set, 'd, ('e, 'd) time, ('a, 'd, 'e) vydra list) window"
    and ('a, 'd, 'e) vydra = VYDRA "(('a, 'd, 'e) vydra_rec \<times> ('d \<times> bool)) option"

definition "iarray_of_list xs = IArray xs"

context
  fixes init :: "'e"
    and run_event :: "'e \<Rightarrow> ('e \<times> ('d :: timestamp \<times> 'a set)) option"
begin

definition t0 :: "('e, 'd) time" where
  "t0 = (case run_event init of None \<Rightarrow> None | Some (e', (t, X)) \<Rightarrow> Some (e', t))"

fun run_t :: "('e, 'd) time \<Rightarrow> (('e, 'd) time \<times> 'd) option" where
  "run_t None = None"
| "run_t (Some (e, t)) = (case run_event e of None \<Rightarrow> Some (None, t)
  | Some (e', (t', X)) \<Rightarrow> Some (Some (e', t'), t))"

fun read_t :: "('e, 'd) time \<Rightarrow> 'd option" where
  "read_t None = None"
| "read_t (Some (e, t)) = Some t"

lemma run_t_read: "run_t x = Some (x', t) \<Longrightarrow> read_t x = Some t"
  by (cases x) (auto split: option.splits)

lemma read_t_run: "read_t x = Some t \<Longrightarrow> \<exists>x'. run_t x = Some (x', t)"
  by (cases x) (auto split: option.splits)

lemma reach_event_t: "reach_sub run_event e vs e'' \<Longrightarrow> run_event e = Some (e', (t, X)) \<Longrightarrow>
  run_event e'' = Some (e''', (t', X')) \<Longrightarrow>
  reach_sub run_t (Some (e', t)) (map fst vs) (Some (e''', t'))"
proof (induction e vs e'' arbitrary: t' X' e''' rule: reach_sub_rev_induct)
  case (2 s s' v vs s'')
  obtain v_t v_X where v_def: "v = (v_t, v_X)"
    by (cases v) auto
  have run_t_s'': "run_t (Some (s'', v_t)) = Some (Some (e''', t'), v_t)"
    by (auto simp: 2(5))
  show ?case
    using reach_sub_app[OF 2(3)[OF 2(4) 2(2)[unfolded v_def]] run_t_s'']
    by (auto simp: v_def)
qed (auto intro: reach_sub.intros)

lemma reach_event_t0_t:
  assumes "reach_sub run_event init vs e''" "run_event e'' = Some (e''', (t', X'))"
  shows "reach_sub run_t t0 (map fst vs) (Some (e''', t'))"
proof -
  have t0_not_None: "t0 \<noteq> None"
    apply (rule reach_sub.cases[OF assms(1)])
    using assms(2)
    by (auto simp: t0_def split: option.splits prod.splits)
  then show ?thesis
    using reach_event_t[OF assms(1) _ assms(2)]
    by (auto simp: t0_def split: option.splits)
qed

definition "run_subs run = (\<lambda>vs. let vs' = map run vs in
  (if (\<exists>x \<in> set vs'. Option.is_none x) then None
   else Some (map (fst \<circ> the) vs', iarray_of_list (map (snd \<circ> snd \<circ> the) vs'))))"

lemma run_subs_lD: "run_subs run vs = Some (vs', bs) \<Longrightarrow>
  length vs' = length vs \<and> IArray.length bs = length vs"
  by (auto simp: run_subs_def Let_def iarray_of_list_def split: option.splits if_splits)

lemma run_subs_vD: "run_subs run vs = Some (vs', bs) \<Longrightarrow> j < length vs \<Longrightarrow>
  \<exists>vj' tj bj. run (vs ! j) = Some (vj', (tj, bj)) \<and> vs' ! j = vj' \<and> IArray.sub bs j = bj"
  apply (cases "run (vs ! j)")
   apply (auto simp: Option.is_none_def run_subs_def Let_def iarray_of_list_def
      split: option.splits if_splits)
  by (metis image_eqI nth_mem)

definition "read_subs read = (\<lambda>vs. let vs' = map read vs in
  (if (\<exists>x \<in> set vs'. Option.is_none x) then None
   else Some (iarray_of_list (map (snd \<circ> the) vs'))))"

lemma read_run_subs:
  assumes read_run: "\<And>s tb. read s = Some tb \<Longrightarrow> \<exists>s'. run s = Some (s', tb)"
    and assm: "read_subs read s = Some tb"
  shows "\<exists>s'. run_subs run s = Some (s', tb)"
proof -
  have run_None: "\<And>x. run x = None \<Longrightarrow> read x = None"
    subgoal for x
      using read_run[of x]
      by (cases "read x") auto
    done
  show ?thesis
    using assm
    apply (auto simp: read_subs_def run_subs_def Let_def iarray_of_list_def
        split: prod.splits option.splits if_splits)
    subgoal for x
      using run_None[of x]
      by force
    subgoal for x
      using read_run[of x]
      by (cases "read x") force+
    done
qed

lemma run_read_subs:
  assumes run_read: "\<And>s s' tb. run s = Some (s', tb) \<Longrightarrow> read s = Some tb"
    and assm: "run_subs run s = Some (s', tb)"
  shows "read_subs read s = Some tb"
proof -
  have run_None: "\<And>x. read x = None \<Longrightarrow> run x = None"
    subgoal for x
      using run_read[of x]
      by (cases "run x") auto
    done
  show ?thesis
    using assm
    apply (auto simp: read_subs_def run_subs_def Let_def iarray_of_list_def
        split: prod.splits option.splits if_splits)
    subgoal for x
      using run_None[of x]
      by force
    subgoal for x
      using run_read[of x]
      by (cases "run x") force+
    done
qed

fun msize_fmla :: "('a, 'b :: timestamp) formula \<Rightarrow> nat"
  and msize_regex :: "('a, 'b) regex \<Rightarrow> nat" where
  "msize_fmla (Bool b) = 0"
| "msize_fmla (Atom a) = 0"
| "msize_fmla (Neg phi) = Suc (msize_fmla phi)"
| "msize_fmla (Bin f phi psi) = Suc (msize_fmla phi + msize_fmla psi)"
| "msize_fmla (Prev I phi) = Suc (msize_fmla phi)"
| "msize_fmla (Next I phi) = Suc (msize_fmla phi)"
| "msize_fmla (Since phi I psi) = Suc (max (msize_fmla phi) (msize_fmla psi))"
| "msize_fmla (Until phi I psi) = Suc (max (msize_fmla phi) (msize_fmla psi))"
| "msize_fmla (MatchP I r) = Suc (msize_regex r)"
| "msize_fmla (MatchF I r) = Suc (msize_regex r)"
| "msize_regex Wild = 0"
| "msize_regex (Test phi) = msize_fmla phi"
| "msize_regex (Plus r s) = max (msize_regex r) (msize_regex s)"
| "msize_regex (Times r s) = max (msize_regex r) (msize_regex s)"
| "msize_regex (Star r) = msize_regex r"

lemma collect_subfmlas_msize: "x \<in> set (collect_subfmlas r []) \<Longrightarrow>
  msize_fmla x \<le> msize_regex r"
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

fun msize_fmla' :: "('a, 'b :: timestamp) formula \<Rightarrow> nat"
  and msize_regex' :: "('a, 'b) regex \<Rightarrow> nat" where
  "msize_fmla' (Bool b) = Suc 0"
| "msize_fmla' (Atom a) = Suc 0"
| "msize_fmla' (Neg phi) = Suc (msize_fmla' phi)"
| "msize_fmla' (Bin f phi psi) = Suc (msize_fmla' phi + msize_fmla' psi)"
| "msize_fmla' (Prev I phi) = Suc (Suc (Suc (Suc (msize_fmla' phi))))"
| "msize_fmla' (Next I phi) = Suc (Suc (Suc (Suc (msize_fmla' phi))))"
| "msize_fmla' (Since phi I psi) =
    Suc (Suc (Suc (Suc (Suc (Suc (Suc (msize_fmla' phi + msize_fmla' psi)))))))"
| "msize_fmla' (Until phi I psi) =
    Suc (Suc (Suc (Suc (Suc (Suc (Suc (msize_fmla' phi + msize_fmla' psi)))))))"
| "msize_fmla' (MatchP I r) = Suc (msize_regex' r)"
| "msize_fmla' (MatchF I r) = Suc (msize_regex' r)"
| "msize_regex' Wild = 0"
| "msize_regex' (Test phi) = Suc (msize_fmla' phi)"
| "msize_regex' (Plus r s) = Suc (msize_regex' r + msize_regex' s)"
| "msize_regex' (Times r s) = Suc (msize_regex' r + msize_regex' s)"
| "msize_regex' (Star r) = Suc (msize_regex' r)"

lemma collect_subfmlas_msize': "x \<in> set (collect_subfmlas r []) \<Longrightarrow>
  msize_fmla' x < msize_regex' r"
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

fun read :: "('a, 'd, 'e) vydra \<Rightarrow> ('d \<times> bool) option" where
  "read (VYDRA None) = None"
| "read (VYDRA (Some (v, x))) = Some x"

fun run :: "nat \<Rightarrow> ('a, 'd, 'e) vydra \<Rightarrow> (('a, 'd, 'e) vydra \<times> ('d \<times> bool)) option" and
  run_rec :: "nat \<Rightarrow> ('a, 'd, 'e) vydra_rec \<Rightarrow> (('a, 'd, 'e) vydra_rec \<times> ('d \<times> bool)) option" where
  "run n (VYDRA None) = None"
| "run n (VYDRA (Some (v, x))) = Some (VYDRA (run_rec n v), x)"
| "run_rec n (VYDRA_Bool b e) = (case run_event e of None \<Rightarrow> None
    | Some (e', (t, _)) \<Rightarrow> Some (VYDRA_Bool b e', (t, b)))"
| "run_rec n (VYDRA_Atom a e) = (case run_event e of None \<Rightarrow> None
    | Some (e', (t, X)) \<Rightarrow> Some (VYDRA_Atom a e', (t, a \<in> X)))"
| "run_rec (Suc n) (VYDRA_Neg v) = (case run n v of None \<Rightarrow> None
    | Some (v', (t, b)) \<Rightarrow> Some (VYDRA_Neg v', (t, \<not>b)))"
| "run_rec (Suc n) (VYDRA_Bin f vl vr) = (case run n vl of None \<Rightarrow> None
    | Some (vl', (t, bl)) \<Rightarrow> (case run n vr of None \<Rightarrow> None
    | Some (vr', (_, br)) \<Rightarrow> Some (VYDRA_Bin f vl' vr', (t, f bl br))))"
| "run_rec (Suc n) (VYDRA_MatchP I transs qf w) =
    (case eval_matchP (init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n), read_subs read)) I w of None \<Rightarrow> None
    | Some ((t, b), w') \<Rightarrow> Some (VYDRA_MatchP I transs qf w', (t, b)))"
| "run_rec (Suc n) (VYDRA_MatchF I transs qf w) =
    (case eval_matchF (init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n), read_subs read)) I w of None \<Rightarrow> None
    | Some ((t, b), w') \<Rightarrow> Some (VYDRA_MatchF I transs qf w', (t, b)))"
| "run_rec _ _ = None"

fun m_sub :: "(nat \<times> ('a, 'd) formula) + (nat \<times> ('a, 'd) formula) \<Rightarrow> nat" where
  "m_sub (Inl (n, phi)) = 1 + 3 * msize_fmla' phi"
| "m_sub (Inr (n, phi)) = 3 * msize_fmla' phi"

function (sequential) sub :: "nat \<Rightarrow> ('a, 'd) formula \<Rightarrow> ('a, 'd, 'e) vydra"
  and sub_rec :: "nat \<Rightarrow> ('a, 'd) formula \<Rightarrow> ('a, 'd, 'e) vydra_rec" where
  "sub n phi = VYDRA (run_rec n (sub_rec n phi))"
| "sub_rec n (Bool b) = VYDRA_Bool b init"
| "sub_rec n (Atom a) = VYDRA_Atom a init"
| "sub_rec (Suc n) (Neg phi) = VYDRA_Neg (sub n phi)"
| "sub_rec (Suc n) (Bin f phi psi) = VYDRA_Bin f (sub n phi) (sub n psi)"
| "sub_rec n (Prev I phi) = sub_rec n (PossiblyP phi I Wild)"
| "sub_rec n (Next I phi) = sub_rec n (PossiblyF Wild I phi)"
| "sub_rec n (Since phi I psi) = sub_rec n (PossiblyP psi I (Star (BaseP phi)))"
| "sub_rec n (Until phi I psi) = sub_rec n (PossiblyF (Star (BaseF phi)) I psi)"
| "sub_rec (Suc n) (MatchP I r) = (let qf = state_cnt r;
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) in
    VYDRA_MatchP I transs qf (init_window (init_args
      ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n), read_subs read))
      t0 (map (sub n) (collect_subfmlas r []))))"
| "sub_rec (Suc n) (MatchF I r) = (let qf = state_cnt r;
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) in
    VYDRA_MatchF I transs qf (init_window (init_args
      ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (run_t, read_t) (run_subs (run n), read_subs read))
      t0 (map (sub n) (collect_subfmlas r []))))"
| "sub_rec _ _ = undefined"
  by pat_completeness auto
termination
  apply (relation "measure m_sub")
  using collect_subfmlas_msize'
            apply (fastforce simp: PossiblyP_def PossiblyF_def BaseP_def BaseF_def)+
  done

lemma run_read_Some: "run n s = Some (s', tb) \<Longrightarrow> read s = Some tb"
  apply (cases s)
  subgoal for x
    by (cases x) (auto split: if_splits)
  done

lemma run_read_None: "run n s = None \<Longrightarrow> read s = None"
  apply (cases s)
  subgoal for x
    by (cases x) (auto split: if_splits)
  done

lemma read_run_Some: "read s = Some tb \<Longrightarrow> \<exists>s'. run n s = Some (s', tb)"
  apply (cases s)
  subgoal for x
    by (cases x) (auto split: if_splits)
  done

lemma read_run_None: "read s = None \<Longrightarrow> run n s = None"
  apply (cases s)
  subgoal for x
    by (cases x) (auto split: if_splits)
  done

end

locale VYDRA_MDL = MDL \<sigma>
  for \<sigma> :: "('a, 'd :: timestamp) trace" +
  fixes init :: "'e"
    and run_event :: "'e \<Rightarrow> ('e \<times> ('d \<times> 'a set)) option"
  assumes run_event_sound: "reach_sub run_event init es s \<Longrightarrow> run_event s = Some (s', (t, X)) \<Longrightarrow>
    t = \<tau> \<sigma> (length es) \<and> X = \<Gamma> \<sigma> (length es)"
begin

abbreviation "ru_t \<equiv> run_t run_event"
abbreviation "l_t0 \<equiv> t0 init run_event"
abbreviation "ru \<equiv> run run_event"
abbreviation "su \<equiv> sub init run_event"

lemma ru_t_event: "reach_sub ru_t t ts t' \<Longrightarrow> t = l_t0 \<Longrightarrow> ru_t t' = Some (t'', x) \<Longrightarrow>
  \<exists>rho e tt. t' = Some (e, tt) \<and> reach_sub run_event init rho e \<and> length rho = Suc (length ts) \<and>
  x = \<tau> \<sigma> (length ts)"
proof (induction t ts t' arbitrary: t'' x rule: reach_sub_rev_induct)
  case (1 s)
  show ?case
    using 1 run_event_sound[OF reach_sub.intros(1)]
    by (auto simp: t0_def split: option.splits intro!: reach_sub.intros)
next
  case (2 s s' v vs s'')
  obtain rho e tt where rho_def: "s' = Some (e, tt)" "reach_sub run_event init rho e"
    "length rho = Suc (length vs)"
    using 2(3)[OF 2(4,2)]
    by auto
  then show ?case
    using 2(2,5) reach_sub_app[OF rho_def(2)] run_event_sound[OF rho_def(2)]
    by (fastforce split: option.splits)
qed

lemma ru_t_tau: "reach_sub ru_t l_t0 ts t' \<Longrightarrow> ru_t t' = Some (t'', x) \<Longrightarrow> x = \<tau> \<sigma> (length ts)"
  using ru_t_event
  by fastforce

inductive wf_vydra :: "('a, 'd) formula \<Rightarrow> ('a, 'd) trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  ('a, 'd :: timestamp, 'e) vydra \<Rightarrow> bool" where
  "wf_vydra phi _ _ _ (VYDRA None)"
| "reach_sub run_event init es sub' \<Longrightarrow> length es = Suc i \<Longrightarrow> t = \<tau> \<sigma> i \<Longrightarrow>
    \<beta> = sat i (Bool b) \<Longrightarrow> wf_vydra (Bool \<beta>) \<sigma> i n
      (VYDRA (Some (VYDRA_Bool b sub', (t, b))))"
| "reach_sub run_event init es sub' \<Longrightarrow> length es = Suc i \<Longrightarrow> t = \<tau> \<sigma> i \<Longrightarrow>
    b = sat i (Atom a) \<Longrightarrow> wf_vydra (Atom a) \<sigma> i n
      (VYDRA (Some (VYDRA_Atom a sub', (t, b))))"
| "wf_vydra phi \<sigma> (Suc i) n v \<Longrightarrow> reach_sub (ru n) (su n phi) vs v \<Longrightarrow> length vs = Suc i \<Longrightarrow>
    t = \<tau> \<sigma> i \<Longrightarrow> b = sat i (Neg phi) \<Longrightarrow> Suc n \<ge> msize_fmla (Neg phi) \<Longrightarrow>
    wf_vydra (Neg phi) \<sigma> i (Suc n) (VYDRA (Some (VYDRA_Neg v, (t, b))))"
| "wf_vydra phi \<sigma> (Suc i) n v \<Longrightarrow> wf_vydra psi \<sigma> (Suc i) n v' \<Longrightarrow>
    reach_sub (ru n) (su n phi) vs v \<Longrightarrow> length vs = Suc i \<Longrightarrow>
    reach_sub (ru n) (su n psi) vs' v' \<Longrightarrow> length vs' = Suc i \<Longrightarrow>
    t = \<tau> \<sigma> i \<Longrightarrow> b = sat i (Bin f phi psi) \<Longrightarrow> Suc n \<ge> msize_fmla (Bin f phi psi) \<Longrightarrow>
    wf_vydra (Bin f phi psi) \<sigma> i (Suc n) (VYDRA (Some (VYDRA_Bin f v v', (t, b))))"
| "valid_window_matchP args I l_t0 (map (su n) (collect_subfmlas r [])) xs (Suc i) w \<Longrightarrow>
    n \<ge> msize_regex r \<Longrightarrow> qf = state_cnt r \<Longrightarrow>
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) \<Longrightarrow>
    args = init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (ru_t, read_t) (run_subs (ru n), read_subs read) \<Longrightarrow>
    t = \<tau> \<sigma> i \<Longrightarrow> b = sat i (MatchP I r) \<Longrightarrow>
    wf_vydra (MatchP I r) \<sigma> i (Suc n) (VYDRA (Some (VYDRA_MatchP I transs qf w, (t, b))))"
| "valid_window_matchF args I l_t0 (map (su n) (collect_subfmlas r [])) xs (Suc i) w \<Longrightarrow>
    n \<ge> msize_regex r \<Longrightarrow> qf = state_cnt r \<Longrightarrow>
    transs = iarray_of_list (build_nfa_impl r (0, qf, [])) \<Longrightarrow>
    args = init_args ({0}, NFA.delta' transs qf, NFA.accept' transs qf)
      (ru_t, read_t) (run_subs (ru n), read_subs read) \<Longrightarrow>
    t = \<tau> \<sigma> i \<Longrightarrow> b = sat i (MatchF I r) \<Longrightarrow>
    wf_vydra (MatchF I r) \<sigma> i (Suc n) (VYDRA (Some (VYDRA_MatchF I transs qf w, (t, b))))"
| "wf_vydra (PossiblyP phi I Wild) \<sigma> i n v \<Longrightarrow> wf_vydra (Prev I phi) \<sigma> i n v"
| "wf_vydra (PossiblyF Wild I phi) \<sigma> i n v \<Longrightarrow> wf_vydra (Next I phi) \<sigma> i n v"
| "wf_vydra (PossiblyP psi I (Star (BaseP phi))) \<sigma> i n v \<Longrightarrow> wf_vydra (Since phi I psi) \<sigma> i n v"
| "wf_vydra (PossiblyF (Star (BaseF phi)) I psi) \<sigma> i n v \<Longrightarrow> wf_vydra (Until phi I psi) \<sigma> i n v"

lemma msize_fmla_transform: "msize_fmla (PossiblyP phi I Wild) = Suc (msize_fmla phi)"
  "msize_fmla (PossiblyF Wild I phi) = Suc (msize_fmla phi)"
  "msize_fmla (PossiblyP psi I (Star (BaseP phi))) = Suc (max (msize_fmla phi) (msize_fmla psi))"
  "msize_fmla (PossiblyF (Star (BaseF phi)) I psi) = Suc (max (msize_fmla phi) (msize_fmla psi))"
  by (auto simp: PossiblyP_def PossiblyF_def BaseP_def BaseF_def)

lemma wf_vydraD: "wf_vydra \<phi> \<sigma> i n v \<Longrightarrow> ru n v = Some (v', (t, b)) \<Longrightarrow>
  t = \<tau> \<sigma> i \<and> b = sat i \<phi>"
  apply (induction \<phi> \<sigma> i n v arbitrary: v' rule: wf_vydra.induct)
  using prev_rewrite next_rewrite since_rewrite until_rewrite
         apply (auto simp: msize_fmla_transform split: option.splits)
  done

lemma reach_run_subs_len:
  assumes reach_subs: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) rho vs"
  shows "length vs = length (collect_subfmlas r [])"
  using reach_subs run_subs_lD
  by (induction "map (su n) (collect_subfmlas r [])" rho vs rule: reach_sub_rev_induct) fastforce+

lemma reach_run_subs_run:
  assumes reach_subs: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) rho vs"
    and subfmla: "j < length (collect_subfmlas r [])" "phi = collect_subfmlas r [] ! j"
  shows "\<exists>rho'. reach_sub (ru n) (su n phi) rho' (vs ! j) \<and> length rho' = length rho"
  using reach_subs subfmla
proof (induction "map (su n) (collect_subfmlas r [])" rho vs rule: reach_sub_rev_induct)
  case 1
  then show ?case
    by (auto intro: reach_sub.intros)
next
  case (2 s' v vs' s'')
  note len_s'_vs = reach_run_subs_len[OF 2(1)]
  obtain rho' where reach_s'_vs: "reach_sub (ru n) (su n phi) rho' (s' ! j)"
    "length rho' = length vs'"
    using 2(2)[OF 2(4,5)]
    by auto
  note run_subslD = run_subs_lD[OF 2(3)]
  note run_subsvD = run_subs_vD[OF 2(3) 2(4)[unfolded len_s'_vs[symmetric]]]
  obtain vj' tj bj where vj'_def: "ru n (s' ! j) = Some (vj', tj, bj)"
    "s'' ! j = vj'" "IArray.sub v j = bj"
    using run_subsvD by auto
  obtain rho'' where rho''_def: "reach_sub (ru n) (su n phi) rho'' (s'' ! j)"
    "length rho'' = Suc (length vs')"
    using reach_sub_app[OF reach_s'_vs(1) vj'_def(1)] vj'_def(2) reach_s'_vs(2)
    by auto
  then show ?case
    using conjunct1[OF run_subslD, unfolded len_s'_vs[symmetric]]
    by auto
qed

lemma IArray_nth_equalityI: "IArray.length xs = length ys \<Longrightarrow>
  (\<And>i. i < IArray.length xs \<Longrightarrow> IArray.sub xs i = ys ! i) \<Longrightarrow> xs = IArray ys"
  by (induction xs arbitrary: ys) (auto intro: nth_equalityI)

lemma bs_sat:
  assumes IH: "\<And>vs v phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow>
    reach_sub (ru n) (su n phi) vs v \<Longrightarrow>
    bounded_future_fmla phi \<Longrightarrow> wf_vydra phi \<sigma> (length vs) n v"
    and reach_subs: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) rho vs"
    and run_subs: "run_subs (ru n) vs = Some (vs', bs)"
    and bf: "bounded_future_regex r"
  shows "bs = iarray_of_list (map (sat (length rho)) (collect_subfmlas r []))"
proof -
  have "\<And>j. j < length (collect_subfmlas r []) \<Longrightarrow>
    IArray.sub bs j = sat (length rho) (collect_subfmlas r [] ! j)"
  proof -
    fix j
    assume lassm: "j < length (collect_subfmlas r [])"
    define phi where "phi = collect_subfmlas r [] ! j"
    have phi_in_set: "phi \<in> set (collect_subfmlas r [])"
      using lassm
      by (auto simp: phi_def)
    have bf_phi: "bounded_future_fmla phi"
      using bf_collect_subfmlas[OF bf phi_in_set]
      by auto
    have wf: "wf_vydra phi \<sigma> (length rho) n (vs ! j)"
      using IH[OF phi_in_set] reach_run_subs_run IH[OF phi_in_set] reach_subs lassm phi_def
        bf_phi
      by fastforce
    show "IArray.sub bs j = sat (length rho) (collect_subfmlas r [] ! j)"
      unfolding phi_def[symmetric]
      using wf_vydraD[OF wf] run_subs_vD[OF run_subs, unfolded reach_run_subs_len[OF reach_subs],
          OF lassm]
      by auto
  qed
  then show ?thesis
    using conjunct2[OF run_subs_lD[OF run_subs]] reach_run_subs_len[OF reach_subs]
    by (auto simp: iarray_of_list_def intro: IArray_nth_equalityI)
qed

lemma sub_induct_rec:
  fixes phi :: "('a, 'd) formula"
  shows "(\<And>b n. P n (Bool b)) \<Longrightarrow> (\<And>a n. P n (Atom a)) \<Longrightarrow>
    (\<And>n phi. msize_fmla phi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P (Suc n) (Neg phi)) \<Longrightarrow>
    (\<And>n f phi psi. msize_fmla (Bin f phi psi) \<le> Suc n \<Longrightarrow> P n phi \<Longrightarrow> P n psi \<Longrightarrow>
      P (Suc n) (Bin f phi psi)) \<Longrightarrow>
    (\<And>n I phi. P n (PossiblyP phi I Wild) \<Longrightarrow> P n (Prev I phi)) \<Longrightarrow>
    (\<And>n I phi. P n (PossiblyF Wild I phi) \<Longrightarrow> P n (Next I phi)) \<Longrightarrow>
    (\<And>n I phi psi. P n (PossiblyP psi I (Star (BaseP phi))) \<Longrightarrow> P n (Since phi I psi)) \<Longrightarrow>
    (\<And>n I phi psi. P n (PossiblyF (Star (BaseF phi)) I psi) \<Longrightarrow> P n (Until phi I psi)) \<Longrightarrow>
    (\<And>n I r. msize_fmla (MatchP I r) \<le> Suc n \<Longrightarrow>
      (\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchP I r)) \<Longrightarrow>
    (\<And>n I r. msize_fmla (MatchF I r) \<le> Suc n \<Longrightarrow>
      (\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchF I r)) \<Longrightarrow> msize_fmla phi \<le> n \<longrightarrow> P n phi"
  apply (rule sub_sub_rec.induct(1))
                apply assumption
               apply (auto simp: msize_fmla_transform)
  done

lemma sub_induct[case_names Bool Atom Neg Bin Prev Next Since Until MatchP MatchF, consumes 1]:
  fixes phi :: "('a, 'd) formula"
  shows "msize_fmla phi \<le> n \<Longrightarrow> (\<And>b n. P n (Bool b)) \<Longrightarrow> (\<And>a n. P n (Atom a)) \<Longrightarrow>
    (\<And>n phi. msize_fmla phi \<le> n \<Longrightarrow> P n phi \<Longrightarrow> P (Suc n) (Neg phi)) \<Longrightarrow>
    (\<And>n f phi psi. msize_fmla (Bin f phi psi) \<le> Suc n \<Longrightarrow> P n phi \<Longrightarrow> P n psi \<Longrightarrow>
      P (Suc n) (Bin f phi psi)) \<Longrightarrow>
    (\<And>n I phi. P n (PossiblyP phi I Wild) \<Longrightarrow> P n (Prev I phi)) \<Longrightarrow>
    (\<And>n I phi. P n (PossiblyF Wild I phi) \<Longrightarrow> P n (Next I phi)) \<Longrightarrow>
    (\<And>n I phi psi. P n (PossiblyP psi I (Star (BaseP phi))) \<Longrightarrow> P n (Since phi I psi)) \<Longrightarrow>
    (\<And>n I phi psi. P n (PossiblyF (Star (BaseF phi)) I psi) \<Longrightarrow> P n (Until phi I psi)) \<Longrightarrow>
    (\<And>n I r. msize_fmla (MatchP I r) \<le> Suc n \<Longrightarrow>
      (\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchP I r)) \<Longrightarrow>
    (\<And>n I r. msize_fmla (MatchF I r) \<le> Suc n \<Longrightarrow>
      (\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n \<Longrightarrow> P n x) \<Longrightarrow>
      P (Suc n) (MatchF I r)) \<Longrightarrow> P n phi"
  using sub_induct_rec[of P phi n]
  by auto

lemma vydra_wf:
  assumes "msize_fmla \<phi> \<le> n" "reach_sub (ru n) (su n \<phi>) vs v" "bounded_future_fmla \<phi>"
  shows "wf_vydra \<phi> \<sigma> (length vs) n v"
  using assms
proof (induction n \<phi> arbitrary: vs v rule: sub_induct)
  case (Bool b n)
  have run_event_init: "\<And>init' t X. run_event init = Some (init', (t, X)) \<Longrightarrow>
    reach_sub run_event init [(t, X)] init' \<and> t = \<tau> \<sigma> 0 \<and> X = \<Gamma> \<sigma> 0"
    using run_event_sound
    by (fastforce intro: reach_sub.intros)
  show ?case
    using Bool
  proof (induction "su n (Bool b)" vs v rule: reach_sub_rev_induct)
    case 1
    then show ?case
      using run_event_init
      by (auto split: option.splits intro!: wf_vydra.intros)
  next
    case (2 s' v vs s'')
    have "\<And>es re re' t X. reach_sub run_event init es re \<Longrightarrow> run_event re = Some (re', (t, X)) \<Longrightarrow>
      t = \<tau> \<sigma> (length es)"
      using run_event_sound
      by fastforce
    then show ?case
      using 2 reach_sub_app[of run_event]
      by (fastforce split: option.splits elim: reach_sub.cases elim!: wf_vydra.cases
          intro!: wf_vydra.intros)
  qed
next
  case (Atom a n)
  have run_event_init: "\<And>init' t X. run_event init = Some (init', (t, X)) \<Longrightarrow>
    reach_sub run_event init [(t, X)] init' \<and> t = \<tau> \<sigma> 0 \<and> X = \<Gamma> \<sigma> 0"
    using run_event_sound
    by (fastforce intro: reach_sub.intros)
  show ?case
    using Atom
  proof (induction "su n (Atom a)" vs v rule: reach_sub_rev_induct)
    case 1
    then show ?case
      using run_event_init
      by (auto split: option.splits intro!: wf_vydra.intros)
  next
    case (2 s' v vs s'')
    have "\<And>es re re' t X. reach_sub run_event init es re \<Longrightarrow> run_event re = Some (re', (t, X)) \<Longrightarrow>
      t = \<tau> \<sigma> (length es) \<and> X = \<Gamma> \<sigma> (length es)"
      using run_event_sound
      by fastforce
    then show ?case
      using 2 reach_sub_app[of run_event]
      by (fastforce split: option.splits elim: reach_sub.cases elim!: wf_vydra.cases
          intro!: wf_vydra.intros)
  qed
next
  case (Neg n x)
  have bf: "bounded_future_fmla x"
    using Neg(4)
    by auto
  have "reach_sub (ru (Suc n)) (su (Suc n) (Neg x)) vs v \<Longrightarrow>
    wf_vydra (Neg x) \<sigma> (length vs) (Suc n) v"
  proof (induction "su (Suc n) (Neg x)" vs v rule: reach_sub_rev_induct)
    case 1
    show ?case
      using Neg(2)[OF reach_sub.intros(2)[OF _ reach_sub.intros(1)], OF _ bf] Neg(1)
      apply (auto split: option.splits intro: wf_vydra.intros)
      subgoal for a t b
        using wf_vydraD[OF Neg(2)[OF reach_sub.intros(1) bf]]
        by (auto intro!: wf_vydra.intros reach_sub.intros(2)[OF _ reach_sub.intros(1)])
      done
  next
    case (2 s' v vs s'')
    obtain vs' v' where vs'_def: "reach_sub (ru n) (su n x) vs' v'" "length vs' = Suc (length vs)"
      "wf_vydra x \<sigma> (length vs') n v'" "n \<ge> msize_fmla x" "s' = VYDRA (Some (VYDRA_Neg v', v))"
      apply (rule wf_vydra.cases[OF 2(2)])
      using 2(3)
      by auto
    have s''_sound: "\<And>w t b. s'' = VYDRA (Some (VYDRA_Neg w, t, b)) \<Longrightarrow>
      t = \<tau> \<sigma> (Suc (length vs)) \<and> b = sat (Suc (length vs)) (Neg x)"
    proof -
      fix w t b
      assume lassm: "s'' = VYDRA (Some (VYDRA_Neg w, (t, b)))"
      have run_v': "ru n v' = Some (w, (t, \<not>b))"
        using 2(3)
        unfolding vs'_def lassm
        by (auto split: if_splits option.splits)
      show "t = \<tau> \<sigma> (Suc (length vs)) \<and> b = sat (Suc (length vs)) (Neg x)"
        using wf_vydraD[OF vs'_def(3) run_v'(1)]
        unfolding vs'_def(2)
        by auto
    qed
    have wf_vydra_s'': "wf_vydra (Neg x) \<sigma> (length (vs @ [v])) (Suc n) s''"
      apply (rule wf_vydra.cases[OF 2(2)])
      using 2(3) vs'_def(3)[unfolded vs'_def(2)]
        Neg(2)[OF reach_sub_app[of "ru n"]] reach_sub_app[of "ru n"] s''_sound bf
      by (fastforce split: option.splits intro!: wf_vydra.intros)+
    moreover have "s'' \<noteq> VYDRA None \<Longrightarrow>
      \<exists>vs' v'. reach_sub (ru n) (su n x) vs' v' \<and> length vs' = Suc (length (vs @ [v]))"
      using wf_vydra_s''
      by (rule wf_vydra.cases) (auto simp: vs'_def split: option.splits)
    ultimately show ?case
      by auto
  qed
  then show ?case
    using Neg
    by (auto intro: wf_vydra.intros)
next
  case (Bin n f x1 x2)
  have "reach_sub (ru (Suc n)) (su (Suc n) (Bin f x1 x2)) vs v \<Longrightarrow>
    wf_vydra (Bin f x1 x2) \<sigma> (length vs) (Suc n) v"
  proof (induction "su (Suc n) (Bin f x1 x2)" vs v rule: reach_sub_rev_induct)
    case 1
    show ?case
      using Bin(2)[OF reach_sub.intros(2)[OF _ reach_sub.intros(1)]]
        Bin(3)[OF reach_sub.intros(2)[OF _ reach_sub.intros(1)]]
      apply (auto split: option.splits intro: wf_vydra.intros)
      subgoal for a t b a' t' b'
        using wf_vydraD[OF Bin(2)[OF reach_sub.intros(1)]]
          wf_vydraD[OF Bin(3)[OF reach_sub.intros(1)]] Bin(1,5)
        by (auto intro!: reach_sub.intros wf_vydra.intros)
      done
  next
    case (2 s' v vs s'')
    note wf_vydra = 2(2)
    obtain vs1 v1 where vs1_def: "reach_sub (ru n) (su n x1) vs1 v1" "length vs1 = Suc (length vs)"
      "wf_vydra x1 \<sigma> (length vs1) n v1"
      apply (rule wf_vydra.cases[OF 2(2)])
      using 2(3)
      by auto
    obtain vs2 v2 where vs2_def: "reach_sub (ru n) (su n x2) vs2 v2" "length vs2 = Suc (length vs)"
      "wf_vydra x2 \<sigma> (length vs2) n v2"
      apply (rule wf_vydra.cases[OF 2(2)])
      using 2(3)
      by auto
    have s'_def: "s' = VYDRA (Some (VYDRA_Bin f v1 v2, v))"
      apply (rule wf_vydra.cases[OF wf_vydra])
      using 2(3) reach_sub_inj[OF vs1_def(1)] reach_sub_inj[OF vs2_def(1)] vs1_def(2) vs2_def(2)
      by (auto split: option.splits elim: wf_vydra.cases)
    have s''_sound: "\<And>w1 w2 t b. s'' = VYDRA (Some (VYDRA_Bin f w1 w2, (t, b))) \<Longrightarrow>
      t = \<tau> \<sigma> (Suc (length vs)) \<and> b = sat (Suc (length vs)) (Bin f x1 x2)"
    proof -
      fix w1 w2 t b
      assume lassm: "s'' = VYDRA (Some (VYDRA_Bin f w1 w2, (t, b)))"
      obtain b1 where run_v1: "ru n v1 = Some (w1, (t, b1))"
        using 2(3)
        unfolding s'_def lassm
        by (auto split: if_splits option.splits)
      obtain b2 where run_v2: "ru n v2 = Some (w2, (t, b2))"
        using 2(3) wf_vydraD[OF vs1_def(3)] wf_vydraD[OF vs2_def(3)]
          vs1_def(2) vs2_def(2)
        unfolding s'_def lassm
        by (auto split: if_splits option.splits)
      then show "t = \<tau> \<sigma> (Suc (length vs)) \<and> b = sat (Suc (length vs)) (Bin f x1 x2)"
        using wf_vydraD[OF vs1_def(3) run_v1] wf_vydraD[OF vs2_def(3) run_v2]
          2(3) run_v1 run_v2
        unfolding vs1_def(2) vs2_def(2) s'_def lassm
        by (auto split: if_splits)
    qed
    have wf_vydra_s'': "wf_vydra (Bin f x1 x2) \<sigma> (length (vs @ [v])) (Suc n) s''"
      using wf_vydra
      apply (rule wf_vydra.cases)
      using 2(3)
            apply (auto)[4]
        defer
        apply (auto)[2]
      using 2(3) Bin(2)[OF reach_sub_app[of "ru n"]] Bin(3)[OF reach_sub_app[of "ru n"]]
        reach_sub_app[of "ru n"] s''_sound Bin(5)
      unfolding s'_def
          apply (auto split: if_splits option.splits prod.splits intro!: wf_vydra.intros)
                 apply fastforce
                apply fastforce
               apply fastforce
              apply fastforce
             apply fastforce
            apply auto
         apply fast
        apply auto
      done
    moreover have "s'' \<noteq> VYDRA None \<Longrightarrow>
      \<exists>vs1 v1 vs2 v2. reach_sub (ru n) (su n x1) vs1 v1 \<and> reach_sub (ru n) (su n x2) vs2 v2 \<and>
      length vs1 = Suc (length (vs @ [v])) \<and> length vs2 = Suc (length (vs @ [v]))"
      using wf_vydra_s''
      by (rule wf_vydra.cases) (auto simp: s'_def split: option.splits)
    ultimately show ?case
      by auto
  qed
  then show ?case
    using Bin(4)
    by (auto intro: wf_vydra.intros)
next
  case (MatchP n I r)
  have msize_regex: "msize_regex r \<le> n"
    using MatchP(1)
    by auto
  have bf: "bounded_future_regex r"
    using MatchP(4)
    by auto
  have "\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n"
    using le_trans[OF collect_subfmlas_msize] MatchP(1)
    by auto
  then have IH: "\<And>vs v phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow>
    reach_sub (ru n) (su n phi) vs v \<Longrightarrow> bounded_future_fmla phi \<Longrightarrow>
    wf_vydra phi \<sigma> (length vs) n v"
    using MatchP(2)
    by auto
  define args where "args = (init_args ({0},
    NFA.delta' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r),
    NFA.accept' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r))
    (ru_t, read_t) (run_subs (ru n), read_subs read))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[OF IH] run_read_subs[of "ru n" read] read_run_subs[of read "ru n"]
      run_read_Some[of run_event] read_run_Some[of _ _ run_event] run_t_read[of run_event]
      read_t_run[of _ _ run_event] ru_t_tau bf
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  define l_sub where "l_sub = map (su n) (collect_subfmlas r [])"
  note args' = args_def[unfolded init_args.simps, symmetric]
  have "reach_sub (ru (Suc n)) (su (Suc n) (MatchP I r)) vs v \<Longrightarrow>
    wf_vydra (MatchP I r) \<sigma> (length vs) (Suc n) v"
  proof (induction "su (Suc n) (MatchP I r)" vs v rule: reach_sub_rev_induct)
    case 1
    define w where "w = init_window args l_t0 (map (su n) (collect_subfmlas r []))"
    note w_def' = w_def[unfolded init_window.simps init_def, symmetric]
    show ?case
    proof (cases "eval_mP I w")
      case None
      then show ?thesis
        by (auto simp: args' w_def' Let_def intro: wf_vydra.intros)
    next
      case (Some a)
      obtain tj' t sj' bs where somes: "w_run_t args (w_tj w) = Some (tj', t)"
        "w_run_sub args (w_sj w) = Some (sj', bs)"
        using Some read_t_run read_sub_run
        by (fastforce simp: Let_def split: option.splits)
      obtain w' where w'_def: "eval_mP I w = Some ((\<tau> \<sigma> 0, sat 0 (MatchP I r)), w')"
        "valid_matchP I l_t0 l_sub [(t, bs)] (Suc 0) w'"
        using valid_eval_matchP[OF valid_init_matchP[folded w_def], unfolded somes]
        by (fastforce simp: l_sub_def)
      show ?thesis
        using w'_def msize_regex
        by (auto simp: args' w_def' l_sub_def Let_def intro!: wf_vydra.intros)
    qed
  next
    case (2 s' v vs s'')
    obtain v_t v_b where v_def: "v = (v_t, v_b)"
      by (cases v) auto
    obtain w t b where s'_def:
      "s' = VYDRA (Some (VYDRA_MatchP I (iarray_of_list transs) qf w, (t, b)))"
      using 2(2,3)
      by (auto simp: qf_def transs_def split: option.splits elim: wf_vydra.cases)
    obtain xs where valid_window: "valid_matchP I l_t0 l_sub xs (Suc (length vs)) w"
      by (rule wf_vydra.cases[OF 2(2)[unfolded s'_def]]) (auto simp: args' l_sub_def s'_def)
    show ?case
    proof (cases "eval_mP I w")
      case None
      then show ?thesis
        using 2(3)[unfolded s'_def]
        by (auto simp: transs_def qf_def args' split: option.splits intro!: wf_vydra.intros)
    next
      case (Some a)
      obtain tj' t' sj' bs where somes: "w_run_t args (w_tj w) = Some (tj', t')"
        "w_run_sub args (w_sj w) = Some (sj', bs)"
        using Some read_t_run read_sub_run
        by (fastforce simp: Let_def split: option.splits)
      obtain w' where w'_def: "eval_mP I w = Some ((\<tau> \<sigma> (Suc (length vs)),
        sat (Suc (length vs)) (MatchP I r)), w')"
        "valid_matchP I l_t0 l_sub (xs @ [(t', bs)]) (Suc (Suc (length vs))) w'"
        using valid_eval_matchP[folded l_sub_def, OF valid_window, unfolded somes]
        by fastforce
      have s''_def: "s'' = VYDRA (Some (VYDRA_MatchP I (iarray_of_list transs) qf w',
        (\<tau> \<sigma> (Suc (length vs)), sat (Suc (length vs)) (MatchP I r))))"
        using 2(3)[unfolded s'_def] w'_def(1)
        by (auto simp: transs_def qf_def args')
      show ?thesis
        unfolding s''_def
        using w'_def(2) msize_regex
        by (auto simp del: eval_matchP.simps simp: qf_def transs_def l_sub_def args'
            intro!: wf_vydra.intros)
    qed
  qed
  then show ?case
    using MatchP(3)
    by auto
next
  case (MatchF n I r)
  have msize_regex: "msize_regex r \<le> n"
    using MatchF(1)
    by auto
  have bf: "bounded_future_regex r" "finite_ts (right I)"
    using MatchF(4)
    by auto
  have "\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n"
    using le_trans[OF collect_subfmlas_msize] MatchF(1)
    by auto
  then have IH: "\<And>vs v phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow>
    reach_sub (ru n) (su n phi) vs v \<Longrightarrow> bounded_future_fmla phi \<Longrightarrow>
    wf_vydra phi \<sigma> (length vs) n v"
    using MatchF(2)
    by auto
  define args where "args = (init_args ({0},
    NFA.delta' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r),
    NFA.accept' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r))
    (ru_t, read_t) (run_subs (ru n), read_subs read))"
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[OF IH] run_read_subs[of "ru n" read] read_run_subs[of read "ru n"]
      run_read_Some[of run_event] read_run_Some[of _ _ run_event] run_t_read[of run_event]
      read_t_run[of _ _ run_event] ru_t_tau bf
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  define l_sub where "l_sub = map (su n) (collect_subfmlas r [])"
  note args' = args_def[unfolded init_args.simps, symmetric]
  have "reach_sub (ru (Suc n)) (su (Suc n) (MatchF I r)) vs v \<Longrightarrow>
    wf_vydra (MatchF I r) \<sigma> (length vs) (Suc n) v"
  proof (induction "su (Suc n) (MatchF I r)" vs v rule: reach_sub_rev_induct)
    case 1
    define w where "w = init_window args l_t0 (map (su n) (collect_subfmlas r []))"
    note w_def' = w_def[unfolded init_window.simps init_def, symmetric]
    show ?case
    proof (cases "eval_mF I w")
      case None
      then show ?thesis
        by (auto simp: args' w_def' Let_def intro: wf_vydra.intros)
    next
      case (Some a)
      obtain w' rho' where w'_def: "eval_mF I w = Some ((\<tau> \<sigma> 0, sat 0 (MatchF I r)), w')"
        "valid_matchF I l_t0 (map (su n) (collect_subfmlas r [])) rho' (Suc 0) w'"
        using valid_eval_matchF_sound[OF valid_init_matchF[folded w_def] _ bf(2)] Some
        by (cases a) (fastforce simp del: eval_matchF.simps)
      show ?thesis
        using w'_def msize_regex
        by (auto simp: args' w_def' l_sub_def Let_def intro!: wf_vydra.intros)
    qed
  next
    case (2 s' v vs s'')
    obtain v_t v_b where v_def: "v = (v_t, v_b)"
      by (cases v) auto
    obtain w t b where s'_def:
      "s' = VYDRA (Some (VYDRA_MatchF I (iarray_of_list transs) qf w, (t, b)))"
      using 2(2,3)
      by (auto simp: qf_def transs_def split: option.splits elim: wf_vydra.cases)
    obtain xs where valid_window: "valid_matchF I l_t0 l_sub xs (Suc (length vs)) w"
      by (rule wf_vydra.cases[OF 2(2)[unfolded s'_def]]) (auto simp: args' l_sub_def s'_def)
    show ?case
    proof (cases "eval_mF I w")
      case None
      then show ?thesis
        using 2(3)[unfolded s'_def]
        by (auto simp: transs_def qf_def args' split: option.splits intro!: wf_vydra.intros)
    next
      case (Some a)
      obtain w' rho' where w'_def: "eval_mF I w = Some ((\<tau> \<sigma> (Suc (length vs)),
        sat (Suc (length vs)) (MatchF I r)), w')"
        "valid_matchF I l_t0 (map (su n) (collect_subfmlas r [])) rho' (Suc (Suc (length vs))) w'"
        using valid_eval_matchF_sound[OF valid_window[unfolded l_sub_def] _ bf(2)] Some
        by (cases a) (fastforce simp del: eval_matchF.simps)
      have s''_def: "s'' = VYDRA (Some (VYDRA_MatchF I (iarray_of_list transs) qf w',
        (\<tau> \<sigma> (Suc (length vs)), sat (Suc (length vs)) (MatchF I r))))"
        using 2(3)[unfolded s'_def] w'_def(1)
        by (auto simp: transs_def qf_def args')
      show ?thesis
        unfolding s''_def
        using w'_def(2) msize_regex
        by (auto simp del: eval_matchP.simps simp: qf_def transs_def l_sub_def args'
            intro!: wf_vydra.intros)
    qed
  qed
  then show ?case
    using MatchF(3)
    by auto
next
  case (Prev n I phi)
  have sub_prev: "su n (Prev I phi) = su n (PossiblyP phi I Wild)"
    by (auto simp: PossiblyP_def)
  show ?case
    using Prev(1)[OF Prev(2)[unfolded sub_prev]] Prev(3)
    by (auto simp: PossiblyP_def intro: wf_vydra.intros)
next
  case (Next n I phi)
  have sub_next: "su n (Next I phi) = su n (PossiblyF Wild I phi)"
    by (auto simp: PossiblyF_def)
  show ?case
    using Next(1)[OF Next(2)[unfolded sub_next]] Next(3)
    by (auto simp: PossiblyF_def intro: wf_vydra.intros)
next
  case (Since n I phi psi)
  have sub_since: "su n (Since phi I psi) = su n (PossiblyP psi I (Star (BaseP phi)))"
    by (auto simp: PossiblyP_def BaseP_def)
  show ?case
    using Since(1)[OF Since(2)[unfolded sub_since]] Since(3)
    by (auto simp: PossiblyP_def BaseP_def intro: wf_vydra.intros)
next
  case (Until n I phi psi)
  have sub_until: "su n (Until phi I psi) = su n (PossiblyF (Star (BaseF phi)) I psi)"
    by (auto simp: PossiblyF_def BaseF_def)
  show ?case
    using Until(1)[OF Until(2)[unfolded sub_until]] Until(3)
    by (auto simp: PossiblyF_def BaseF_def intro: wf_vydra.intros)
qed

lemma reach_subs_run_lD: "reach_sub (run_subs (ru n)) vs ws vs' \<Longrightarrow>
  length vs = length vs'"
  by (induction vs ws vs' rule: reach_sub_rev_induct)
     (auto simp: run_subs_def Let_def split: option.splits if_splits)

lemma reach_subs_run_vD: "reach_sub (run_subs (ru n)) vs ws vs' \<Longrightarrow>
  i < length vs \<Longrightarrow> (\<exists>ys. reach_sub (ru n) (vs ! i) ys (vs' ! i) \<and> length ys = length ws)"
proof (induction vs ws vs' rule: reach_sub_rev_induct)
  case (2 s s' bs bss s'')
  obtain ys where ys_def: "reach_sub (ru n) (s ! i) ys (s' ! i)"
    "length s = length s'" "length ys = length bss"
    using reach_subs_run_lD[OF 2(1)] 2(3)[OF 2(4)]
    by auto
  obtain tb where tb_def: "ru n (s' ! i) = Some (s'' ! i, tb)"
    using run_subs_vD[OF 2(2) 2(4)[unfolded ys_def(2)]]
    by auto
  show ?case
    using reach_sub_app[OF ys_def(1) tb_def(1)] ys_def(2,3) tb_def
    by auto
qed (auto intro: reach_sub.intros)

lemma reach_subs_runI:
  assumes "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow>
    \<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and> length ws = length vs \<and> ru n v \<noteq> None"
    "reach_sub run_event init vs e" "run_event e = Some (e', (t, X))"
    and n_def: "n \<ge> msize_regex r"
  shows "\<exists>ws v. reach_sub (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) ws v \<and>
    length ws = length vs \<and> run_subs (ru n) v \<noteq> None"
  using assms
proof (induction vs arbitrary: e e' t X rule: rev_induct)
  case Nil
  have e_init: "e = init"
    using Nil(2)
    by (auto elim: reach_sub.cases)
  have "run_subs (ru n) (map (su n) (collect_subfmlas r [])) \<noteq> None"
    using collect_subfmlas_msize[of _ r] Nil(1)
    by (fastforce simp: run_subs_def Let_def Nil(3)[unfolded e_init] n_def
        split: option.splits elim: reach_sub.cases)
  then show ?case
    by (fastforce intro: reach_sub.intros)
next
  case (snoc x xs)
  obtain s' x_t x_X where s'_def: "reach_sub run_event init xs s'"
    "run_event s' = Some (e, (x_t, x_X))"
    using reach_sub_split_last[OF snoc(3)]
    by fastforce
  have IH': "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow>
      \<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and> length ws = length xs \<and> ru n v \<noteq> None"
  proof -
    fix phi
    assume lassm: "phi \<in> set (collect_subfmlas r [])"
    obtain ws v where ws_def: "reach_sub (ru n) (su n phi) ws v"
      "length ws = length (xs @ [x])" "ru n v \<noteq> None"
      using snoc(2)[OF lassm]
      by auto
    obtain y ys where ws_snoc: "ws = ys @ [y]"
      using ws_def(2)
      by (cases ws rule: rev_cases) auto
    show "\<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and> length ws = length xs \<and> ru n v \<noteq> None"
      using reach_sub_split_last[OF ws_def(1)[unfolded ws_snoc]] ws_def(2) ws_snoc
      by fastforce
  qed
  obtain ws v where ws_def: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) ws v" "length ws = length xs"
    "run_subs (ru n) v \<noteq> None"
    using snoc(1)[OF _ s'_def n_def] IH'
    by blast
  obtain v' tb where v'_def: "run_subs (ru n) v = Some (v', tb)"
    using ws_def(3)
    by auto
  note reach' = reach_sub_app[OF ws_def(1) v'_def]
  note len_v'_vs = reach_subs_run_lD[OF reach', symmetric]
  have run_v'_vs: "\<And>x. x \<in> set v' \<Longrightarrow> ru n x \<noteq> None"
  proof -
    fix x
    assume lassm: "x \<in> set v'"
    obtain i where i_def: "x = v' ! i" "i < length v'"
      using lassm
      by (metis in_set_conv_nth)
    obtain ys where ys_def: "reach_sub (ru n) (map (su n) (collect_subfmlas r []) ! i) ys (v' ! i)"
      "length ys = Suc (length ws)"
      using reach_subs_run_vD[OF reach' i_def(2)[unfolded len_v'_vs]]
      by auto
    obtain zs z where zs_def: "reach_sub (ru n) (su n (collect_subfmlas r [] ! i)) zs z"
      "length zs = Suc (length xs)" "ru n z \<noteq> None"
      using snoc(2) i_def(2)[unfolded len_v'_vs]
      by force
    have z_def: "z = v' ! i"
      using reach_sub_inj ys_def(1) zs_def(1) ys_def(2) zs_def(2) ws_def(2) i_def(2) len_v'_vs
      by fastforce
    show "ru n x \<noteq> None"
      using zs_def(3) z_def i_def
      by auto
  qed
  then have "run_subs (ru n) v' \<noteq> None"
    using snoc(4) reach_subs_run_vD[OF reach'] len_v'_vs
      collect_subfmlas_msize[of _ r]
    by (fastforce simp: run_subs_def Let_def n_def split: option.splits)
  then show ?case
    using reach_sub_app[OF ws_def(1) v'_def] ws_def(2)
    by fastforce
qed

lemma reach_sub_takeWhile: "reach_sub r s vs s' \<Longrightarrow> r s' = Some (s'', v) \<Longrightarrow> \<not>f v \<Longrightarrow>
  vs' = takeWhile f vs \<Longrightarrow>
  \<exists>t' t'' v'. reach_sub r s vs' t' \<and> r t' = Some (t'', v') \<and> \<not>f v' \<and>
  reach_sub r t' (drop (length vs') vs) s'"
  by (induction s vs s' arbitrary: vs' rule: reach_sub.induct) (auto intro: reach_sub.intros)

lemma vydra_complete_sub:
  assumes prefix: "reach_sub run_event e0 vs e" "run_event e = Some (e', (t, X))"
    and prefix': "reach_sub run_event e vs' f" "run_event f = Some (f', (t', X'))"
    and e0: "e0 = init"
    and reach: "\<not>t' \<le> t + FR_fmla \<phi>" "bounded_future_fmla \<phi>"
    and n_ge: "n \<ge> msize_fmla \<phi>"
  shows "\<exists>ws v. reach_sub (ru n) (su n \<phi>) ws v \<and> length ws = length vs \<and> ru n v \<noteq> None"
  using n_ge prefix prefix' e0 reach
proof (induction n \<phi> arbitrary: vs e e' t X vs' f f' t' X' rule: sub_induct)
  case (Bool x n)
  show ?case
    using Bool
  proof (induction e0 vs e arbitrary: e' t X vs' f f' t' X' rule: reach_sub_rev_induct)
    case (2 s s' v vs s'')
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    note reach' = reach_sub_app[OF 2(1,2), unfolded 2(7)]
    have msize: "msize_fmla (Bool x) \<le> n"
      by auto
    have v_t_le: "v_t \<le> t"
      using run_event_sound[OF reach' 2(4)]
        run_event_sound[OF 2(1)[unfolded 2(7)] 2(2)[unfolded v_def]]
      by auto
    have ets_v_t: "\<not>t' \<le> v_t + FR_fmla (Bool x)"
      using 2(8) add_mono_comm[OF v_t_le, of "FR_fmla (Bool x)"] order.trans
      by auto
    obtain ws cv cv' ctb where ws_def: "reach_sub (ru n) (su n (Bool x)) ws cv"
      "length ws = length vs" "ru n cv = Some (cv', ctb)"
      using 2(3)[OF 2(2)[unfolded v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6,7) ets_v_t 2(9)]
      by auto
    note reach = reach_sub_app[OF ws_def(1,3)]
    obtain tb where cv_def: "cv = VYDRA (Some ((VYDRA_Bool x s''), tb))"
      apply (rule wf_vydra.cases[OF vydra_wf[OF msize ws_def(1) 2(9)]])
      using reach_sub_inj[OF reach'] ws_def(3) 2(4)
      by (auto simp: ws_def(2) split: option.splits)
    have "ru n cv' \<noteq> None"
      using ws_def(3)[unfolded cv_def] 2(4)
      by auto
    then show ?case
      using reach ws_def(2)
      by fastforce
  qed (auto intro: reach_sub.intros)
next
  case (Atom x n)
  show ?case
    using Atom
  proof (induction e0 vs e arbitrary: e' t X vs' f f' t' X' rule: reach_sub_rev_induct)
    case (2 s s' v vs s'')
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    note reach' = reach_sub_app[OF 2(1,2), unfolded 2(7)]
    have msize: "msize_fmla (Atom x) \<le> n"
      by auto
    have v_t_le: "v_t \<le> t"
      using run_event_sound[OF reach' 2(4)]
        run_event_sound[OF 2(1)[unfolded 2(7)] 2(2)[unfolded v_def]]
      by auto
    have ets_v_t: "\<not>t' \<le> v_t + FR_fmla (Atom x)"
      using 2(8) add_mono_comm[OF v_t_le, of "FR_fmla (Atom x)"] order.trans
      by auto
    obtain ws cv cv' ctb where ws_def: "reach_sub (ru n) (su n (Atom x)) ws cv"
      "length ws = length vs" "ru n cv = Some (cv', ctb)"
      using 2(3)[OF 2(2)[unfolded v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6,7) ets_v_t 2(9)]
      by auto
    note reach = reach_sub_app[OF ws_def(1,3)]
    obtain tb where cv_def: "cv = VYDRA (Some ((VYDRA_Atom x s''), tb))"
      apply (rule wf_vydra.cases[OF vydra_wf[OF msize ws_def(1) 2(9)]])
      using reach_sub_inj[OF reach'] ws_def(3) 2(4)
      by (auto simp: ws_def(2) split: option.splits)
    have "ru n cv' \<noteq> None"
      using ws_def(3)[unfolded cv_def] 2(4)
      by auto
    then show ?case
      using reach ws_def(2)
      by fastforce
  qed (auto intro: reach_sub.intros)
next
  case (Neg n x)
  note IH = Neg(2)[unfolded e0, OF _ _ _ _ refl]
  have msize: "msize_fmla (Neg x) \<le> Suc n"
    using Neg(1)
    by auto
  show ?case
    using Neg(3,4,5,6,7,8,9)
  proof (induction e0 vs e arbitrary: e' t X vs' f f' t' X' rule: reach_sub_rev_induct)
    case (1 s)
    show ?case
      using IH[OF reach_sub.intros(1)[unfolded 1(4)] 1(1,2,3)[unfolded 1(4)]] 1(5,6)
      by (auto elim!: reach_sub.cases intro: reach_sub.intros(1))
  next
    case (2 s s' v vs s'')
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    note reach' = reach_sub_app[OF 2(1,2), unfolded 2(7)]
    have v_t_le: "v_t \<le> t"
      using run_event_sound[OF reach' 2(4)]
        run_event_sound[OF 2(1)[unfolded 2(7)] 2(2)[unfolded v_def]]
      by auto
    have ets_v_t: "\<not>t' \<le> v_t + FR_fmla (Neg x)"
      using 2(8) add_mono_comm[OF v_t_le] order.trans
      by auto
    obtain ys sv sv' stb where ys_def: "reach_sub (ru n) (su n x) ys sv"
      "length ys = length vs" "ru n sv = Some (sv', stb)"
      using IH[OF 2(1,2)[unfolded 2(7) v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6)] ets_v_t 2(9)
      by auto
    obtain ws cv cv' ctb where ws_def: "reach_sub (ru (Suc n)) (su (Suc n) (Neg x)) ws cv"
      "length ws = length vs" "ru (Suc n) cv = Some (cv', ctb)"
      using 2(3)[OF 2(2)[unfolded v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6,7) ets_v_t 2(9)]
      by auto
    note reach = reach_sub_app[OF ys_def(1,3)]
    obtain tb where cv_def: "cv = VYDRA (Some ((VYDRA_Neg sv'), tb))"
      apply (rule wf_vydra.cases[OF vydra_wf[OF msize ws_def(1) 2(9)]])
      using reach_sub_inj[OF reach] ws_def(3)
      by (auto simp: ws_def(2) ys_def(2) split: option.splits)
    obtain zs va where zs_def: "reach_sub (ru n) (su n x) zs va" "length zs = length (vs @ [v])"
      "ru n va \<noteq> None"
      using IH[OF reach_sub_app[OF 2(1,2), unfolded 2(7)] 2(4) 2(5,6)[unfolded 2(7) v_def]] 2(8,9)
      by auto
    have run_sv': "ru n sv' \<noteq> None"
      using reach_sub_inj[OF reach zs_def(1)] ws_def(2) ys_def(2) zs_def(2,3)
      by auto
    have "ru (Suc n) cv' \<noteq> None"
      using ws_def(3)[unfolded cv_def] run_sv' vydra_wf[OF Neg(1) reach] 2(9)
      by (auto split: option.splits if_splits)
    then show ?case
      using reach_sub_app[OF ws_def(1,3)] ws_def(2)
      by fastforce
  qed
next
  case (Bin n op x1 x2)
  have msize: "msize_fmla x1 \<le> n" "msize_fmla x2 \<le> n"
    using Bin(1)
    by auto
  note IH1 = Bin(2)[unfolded e0, OF _ _ _ _ refl]
  note IH2 = Bin(3)[unfolded e0, OF _ _ _ _ refl]
  show ?case
    using Bin(4,5,6,7,8,9,10)
  proof (induction e0 vs e arbitrary: e' t X vs' f f' t' X' rule: reach_sub_rev_induct)
    case (1 s)
    have "\<not>t' \<le> t + FR_fmla x1" "\<not>t' \<le> t + FR_fmla x2"
      using 1(5)
      by (auto simp add: add_mono order_trans)
    then show ?case
      using IH1[OF reach_sub.intros(1)[unfolded 1(4)] 1(1,2,3)[unfolded 1(4)]]
        IH2[OF reach_sub.intros(1)[unfolded 1(4)] 1(1,2,3)[unfolded 1(4)]] 1(6)
      by (auto elim!: reach_sub.cases intro: reach_sub.intros(1))
  next
    case (2 s s' v vs s'')
    have ets_t': "\<not>t' \<le> t + FR_fmla x1" "\<not>t' \<le> t + FR_fmla x2"
      using 2(8)
      by (auto simp add: add_mono order_trans)
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    note reach' = reach_sub_app[OF 2(1,2), unfolded 2(7)]
    have v_t_le: "v_t \<le> t"
      using run_event_sound[OF reach' 2(4)]
        run_event_sound[OF 2(1)[unfolded 2(7)] 2(2)[unfolded v_def]]
      by auto
    have ets_v_t: "\<not>t' \<le> v_t + FR_fmla x1" "\<not>t' \<le> v_t + FR_fmla x2"
      "\<not>t' \<le> v_t + FR_fmla (Bin op x1 x2)"
      using 2(8) ets_t' add_mono_comm[OF v_t_le] order.trans
      by (auto simp add: add_mono order_trans)
    obtain ys1 sv1 sv1' stb1 where ys1_def: "reach_sub (ru n) (su n x1) ys1 sv1"
      "length ys1 = length vs" "ru n sv1 = Some (sv1', stb1)"
      using IH1[OF 2(1,2)[unfolded 2(7) v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6)] ets_v_t 2(9)
      by auto
    obtain ys2 sv2 sv2' stb2 where ys2_def: "reach_sub (ru n) (su n x2) ys2 sv2"
      "length ys2 = length vs" "ru n sv2 = Some (sv2', stb2)"
      using IH2[OF 2(1,2)[unfolded 2(7) v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6)] ets_v_t 2(9)
      by auto
    obtain ws cv cv' ctb where ws_def: "reach_sub (ru (Suc n)) (su (Suc n) (Bin op x1 x2)) ws cv"
      "length ws = length vs" "ru (Suc n) cv = Some (cv', ctb)"
      using 2(3)[OF 2(2)[unfolded v_def] reach_sub.intros(2)[OF 2(2,5)] 2(6,7)] ets_v_t 2(9)
      by auto
    note reach1 = reach_sub_app[OF ys1_def(1,3)]
    note reach2 = reach_sub_app[OF ys2_def(1,3)]
    obtain tb where cv_def: "cv = VYDRA (Some ((VYDRA_Bin op sv1' sv2'), tb))"
      apply (rule wf_vydra.cases[OF vydra_wf[OF Bin(1) ws_def(1) 2(9)]])
      using reach_sub_inj[OF reach1] reach_sub_inj[OF reach2] ws_def(3)
      by (auto simp: ws_def(2) ys1_def(2) ys2_def(2) split: option.splits)
    obtain zs1 va1 where zs1_def: "reach_sub (ru n) (su n x1) zs1 va1"
      "length zs1 = length (vs @ [v])" "ru n va1 \<noteq> None"
      using IH1[OF reach_sub_app[OF 2(1,2), unfolded 2(7)] 2(4) 2(5,6)[unfolded 2(7) v_def]]
        ets_t' 2(9)
      by auto
    obtain zs2 va2 where zs2_def: "reach_sub (ru n) (su n x2) zs2 va2"
      "length zs2 = length (vs @ [v])" "ru n va2 \<noteq> None"
      using IH2[OF reach_sub_app[OF 2(1,2), unfolded 2(7)] 2(4) 2(5,6)[unfolded 2(7) v_def]]
        ets_t' 2(9)
      by auto
    have run_sv': "ru n sv1' \<noteq> None" "ru n sv2' \<noteq> None"
      using reach_sub_inj[OF reach1 zs1_def(1)] ws_def(2) ys1_def(2) zs1_def(2,3)
        reach_sub_inj[OF reach2 zs2_def(1)] ys2_def(2) zs2_def(2,3)
      by auto
    have "ru (Suc n) cv' \<noteq> None"
      using ws_def(3)[unfolded cv_def] run_sv' vydra_wf[OF msize(1) reach1]
        vydra_wf[OF msize(2) reach2] 2(9)
      by (auto split: option.splits if_splits)
    then show ?case
      using reach_sub_app[OF ws_def(1,3)] ws_def(2)
      by fastforce
  qed
next
  case (MatchP n I r)
  have msize_regex: "msize_regex r \<le> n"
    using MatchP(1)
    by auto
  have bf: "bounded_future_regex r"
    using MatchP(9)
    by auto
  define args where "args = (init_args ({0},
    NFA.delta' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r),
    NFA.accept' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r))
    (ru_t, read_t) (run_subs (ru n), read_subs read))"
  have msize_sub: "\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n"
    using le_trans[OF collect_subfmlas_msize] MatchP(1)
    by auto
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[OF vydra_wf, OF msize_sub] run_read_subs[of "ru n" read]
      read_run_subs[of read "ru n"] run_read_Some[of run_event] read_run_Some[of _ _ run_event]
      run_t_read[of run_event] read_t_run[of _ _ run_event] ru_t_tau bf
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  define l_sub where "l_sub = map (su n) (collect_subfmlas r [])"
  note args' = args_def[unfolded init_args.simps, symmetric]
  have run_args: "w_run_t args = ru_t" "w_run_sub args = run_subs (ru n)"
    by (auto simp: args_def)
  have sub: "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow> \<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and>
    length ws = length vs \<and> ru n v \<noteq> None"
  proof -
    fix phi
    assume lassm: "phi \<in> set (collect_subfmlas r [])"
    have FR_le: "FR_fmla phi \<le> FR_fmla (MatchP I r)"
      using FR_collect_subfmlas[OF lassm]
      by auto
    have ets_t': "\<not>t' \<le> t + FR_fmla phi"
      using MatchP(8) add_mono[OF FR_le, of t] order.trans
      by auto
    show "\<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and> length ws = length vs \<and> ru n v \<noteq> None"
      using MatchP ets_t' bf_collect_subfmlas lassm msize_sub
      by fastforce
  qed
  have subs: "\<exists>ws v. reach_sub (run_subs (ru n))
    (map (su n) (collect_subfmlas r [])) ws v \<and> length ws = length vs \<and>
    run_subs (ru n) v \<noteq> None"
    using reach_subs_runI[OF sub MatchP(3,4)[unfolded MatchP(7)]] msize_regex
    by auto
  show ?case
    using MatchP(3,4,7) subs
  proof (induction e0 vs e arbitrary: e' t X vs' f f' t' X' rule: reach_sub_rev_induct)
    case (1 s)
    define w where "w = init_window args l_t0 (map (su n) (collect_subfmlas r []))"
    note w_def' = w_def[unfolded init_window.simps init_def, symmetric]
    have "ru_t l_t0 \<noteq> None" "run_subs (ru n) l_sub \<noteq> None"
      using 1
      by (fastforce simp: t0_def l_sub_def elim: reach_sub.cases split: option.splits)+
    moreover have "w_run_t args (w_tj w) = ru_t l_t0"
      "w_run_sub args (w_sj w) = run_subs (ru n) l_sub"
      by (auto simp: args_def w_def l_sub_def)
    ultimately have "eval_mP I w \<noteq> None"
      using valid_eval_matchP[OF valid_init_matchP[folded w_def]]
      by fastforce
    then show ?case
      by (auto simp: args' init_def w_def Let_def split: option.splits intro: reach_sub.intros)
  next
    case (2 s s' v vs s'')
    obtain ys va where ys_def: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) ys va" "length ys = length (vs @ [v])"
      "run_subs (ru n) va \<noteq> None"
      using 2
      by blast
    obtain z zs where ys_snoc: "ys = zs @ [z]"
      using ys_def(2)
      by (cases ys rule: rev_cases) auto
    obtain wp where wp_def: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) zs wp" "run_subs (ru n) wp = Some (va, z)"
      using reach_sub_split_last[OF ys_def(1)[unfolded ys_snoc]]
      by auto
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    obtain ws vb where ws_def: "reach_sub (ru (Suc n)) (su (Suc n) (MatchP I r)) ws vb"
      "length ws = length vs" "ru (Suc n) vb \<noteq> None"
      using 2(3)[OF 2(2)[unfolded v_def]] wp_def ys_snoc ys_def(2) 2
      by fastforce
    obtain w tb where vb_def:
      "vb = VYDRA (Some (VYDRA_MatchP I (iarray_of_list transs) qf w, tb))"
      using vydra_wf[OF MatchP(1) ws_def(1) MatchP(9)] ws_def(3)
      by (auto simp: qf_def transs_def elim!: wf_vydra.cases)
    obtain xs where xs_def: "valid_matchP I l_t0 l_sub xs (Suc (length ws)) w"
      by (rule wf_vydra.cases[OF vydra_wf[OF MatchP(1) ws_def(1) MatchP(9), unfolded vb_def]])
         (auto simp: args' l_sub_def)
    have csj_va: "w_sj w = va"
      using reach_sub_inj[OF ys_def(1), folded l_sub_def,
        OF valid_window_matchP_reach_sj[OF xs_def(1), unfolded run_args]]
        ws_def(2) ys_def(2) valid_window_matchP_len_rho[OF xs_def(1)]
      by auto
    obtain v_t v_X where v_def: "v = (v_t, v_X)"
      by (cases v) auto
    have "w_tj w = Some (e', t)"
      using reach_sub_inj[OF reach_event_t0_t[OF reach_sub_app[OF 2(1,2), unfolded 2(5)] 2(4)]
        valid_window_matchP_reach_tj[OF xs_def(1), unfolded run_args]]
        ws_def(2) valid_window_matchP_len_rho[OF xs_def(1)]
      by auto
    then have "ru_t (w_tj w) \<noteq> None"
      by (auto split: option.splits)
    then have "eval_mP I w \<noteq> None"
      using valid_eval_matchP[OF xs_def(1)[unfolded csj_va l_sub_def], unfolded run_args] ys_def(3)
      unfolding csj_va
      by fast
    then obtain w' tb' where w'_def: "ru (Suc n) vb = Some (VYDRA (Some (w', tb')), tb)"
      unfolding vb_def
      by (auto simp: args' qf_def transs_def)
    have "ru (Suc n) (VYDRA (Some (w', tb'))) \<noteq> None"
      using vydra_wf[OF MatchP(1) reach_sub_app[OF ws_def(1) w'_def] MatchP(9)]
      by auto
    then show ?case
      using reach_sub_app[OF ws_def(1) w'_def] ws_def(2)
      by fastforce
  qed
next
  case (MatchF n I r)
  have msize_regex: "msize_regex r \<le> n"
    using MatchF(1)
    by auto
  have bf: "bounded_future_regex r"
    using MatchF(9)
    by auto
  define args where "args = (init_args ({0},
    NFA.delta' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r),
    NFA.accept' (iarray_of_list (build_nfa_impl r (0, state_cnt r, []))) (state_cnt r))
    (ru_t, read_t) (run_subs (ru n), read_subs read))"
  have msize_sub: "\<And>x. x \<in> set (collect_subfmlas r []) \<Longrightarrow> msize_fmla x \<le> n"
    using le_trans[OF collect_subfmlas_msize] MatchF(1)
    by auto
  interpret MDL_window \<sigma> r l_t0 "map (su n) (collect_subfmlas r [])" args
    using bs_sat[OF vydra_wf, OF msize_sub] run_read_subs[of "ru n" read]
      read_run_subs[of read "ru n"] run_read_Some[of run_event] read_run_Some[of _ _ run_event]
      run_t_read[of run_event] read_t_run[of _ _ run_event] ru_t_tau bf
    unfolding args_def iarray_of_list_def
    by unfold_locales auto
  define l_sub where "l_sub = map (su n) (collect_subfmlas r [])"
  note args' = args_def[unfolded init_args.simps, symmetric]
  have run_args: "w_run_t args = ru_t" "w_read_t args = read_t" "w_run_sub args = run_subs (ru n)"
    "w_read_sub args = read_subs read"
    by (auto simp: args_def)
  have not_ets_tt: "\<not> (case (t', X') of (tt, X) \<Rightarrow> tt \<le> t + right I)"
    using MatchF(8) add_mono[OF FR_pos(2), of "t + right I"] order.trans
    by (auto simp: add.assoc)
  define rho where rho_def: "rho = takeWhile (\<lambda>(tt, X). tt \<le> t + right I) vs'"
  obtain g g' g_t g_X where g_def: "reach_sub run_event e rho g"
    "reach_sub run_event g (drop (length rho) vs') f"
    "run_event g = Some (g', (g_t, g_X))" "\<not>g_t \<le> t + right I"
    using reach_sub_takeWhile[OF MatchF(5,6) not_ets_tt rho_def]
    by auto
  obtain rho' rho_last where rho_split: "rho = rho' @ [rho_last]"
    using g_def(1,3,4) MatchF(4) right_I_add_mono
    by (cases rho rule: rev_cases) (auto elim!: reach_sub.cases)+
  obtain rho_last_t rho_last_X where rho_last_def: "rho_last = (rho_last_t, rho_last_X)"
    by (cases rho_last) auto
  obtain h where h_def: "reach_sub run_event e rho' h"
    "run_event h = Some (g, (rho_last_t, rho_last_X))"
    using reach_sub_split_last[OF g_def(1)[unfolded rho_split rho_last_def]]
    by auto
  have "(rho_last_t, rho_last_X) \<in> set rho"
    unfolding rho_split rho_last_def
    by auto
  then have ets_rho_last_t: "rho_last_t \<le> t + right I"
    using set_takeWhileD
    unfolding rho_def
    by fastforce
  note reach_sub_eg = reach_event_t[OF g_def(1) MatchF(4) g_def(3)]
  note reach_sub_e = reach_event_t0_t[OF MatchF(3)[unfolded MatchF(7)] MatchF(4)]
  note reach_sub_t = reach_sub_trans[OF reach_sub_e reach_sub_eg]
  note reach_sub_init_vs_rho' = reach_sub_trans[OF MatchF(3)[unfolded MatchF(7)] h_def(1)]
  have sub: "\<And>phi. phi \<in> set (collect_subfmlas r []) \<Longrightarrow> \<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and>
    length ws = length (vs @ rho') \<and> ru n v \<noteq> None"
  proof -
    fix phi
    assume lassm: "phi \<in> set (collect_subfmlas r [])"
    have FR_le: "FR_fmla phi \<le> FR_regex r"
      using FR_collect_subfmlas[OF lassm]
      by auto
    have ets_t': "\<not>t' \<le> rho_last_t + FR_fmla phi"
      using MatchF(8) order.trans add_mono[OF FR_le, of rho_last_t]
        add_mono[OF ets_rho_last_t, of "FR_regex r"]
      unfolding FR_fmla.simps add.assoc
      by (metis add.commute group_cancel.add1)
    show "\<exists>ws v. reach_sub (ru n) (su n phi) ws v \<and> length ws = length (vs @ rho') \<and> ru n v \<noteq> None"
      using MatchF(2)[unfolded MatchF(7), OF lassm msize_sub[OF lassm] reach_sub_init_vs_rho'
        h_def(2) reach_sub.intros(2)[OF h_def(2) g_def(2)] MatchF(6) refl ets_t']
        bf_collect_subfmlas[OF bf lassm]
      by auto
  qed
  have subs: "\<exists>ws v. reach_sub (run_subs (ru n)) (map (su n) (collect_subfmlas r [])) ws v \<and>
  length ws = length (vs @ rho)"
    using reach_subs_runI[OF sub reach_sub_init_vs_rho' h_def(2) msize_regex] reach_sub_app
    by (fastforce simp: rho_split)
  show ?case
    using MatchF(3,7) reach_sub_e reach_sub_t subs g_def(4)
  proof (induction e0 vs e arbitrary: e' t g' g_t rho rule: reach_sub_rev_induct)
    case (1 s)
    have l_t0_def: "l_t0 = Some (e', t)"
      using 1(2)
      by (auto elim: reach_sub.cases)
    have read_l_t0: "read_t l_t0 = Some t"
      unfolding l_t0_def
      by auto
    have read_tj''': "read_t (Some (g', g_t)) = Some g_t"
      by auto
    obtain ws sj''' where ws_def: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) ws sj'''" "length ws = length rho"
      using 1(4)
      by fastforce
    define rho' where "rho' = zip (map fst rho) ws"
    have reach_sub_r_t: "reach_sub ru_t l_t0 (map fst rho') (Some (g', g_t))"
      using 1(3) ws_def(2)
      unfolding rho'_def
      by auto
    have reach_sub_run_sub: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) (map snd rho') sj'''"
      using ws_def
      unfolding rho'_def
      by auto
    define w where "w = init_window args l_t0 (map (su n) (collect_subfmlas r []))"
    note w_def' = w_def[unfolded init_window.simps init_def, symmetric]
    have w_tj_sj: "w_ti w = l_t0" "w_tj w = l_t0" "w_sj w = l_sub"
      by (auto simp: w_def l_sub_def)
    have "eval_mF I w \<noteq> None"
      using valid_eval_matchF_complete[OF valid_init_matchF[folded w_def],
          unfolded run_args w_tj_sj, OF reach_sub_r_t reach_sub_run_sub[folded l_sub_def]
          read_l_t0 read_tj''' 1(5)]
      by auto
    then show ?case
      by (auto simp: w_def args' init_def Let_def intro: reach_sub.intros)
  next
    case (2 s s' v vs s'')
    have reach_sub_r_l_t0: "reach_sub ru_t l_t0 (map fst vs @ [fst v]) (Some (e', t))"
      using 2(5)
      by auto
    obtain ys sj''' where ys_def: "reach_sub (run_subs (ru n))
      (map (su n) (collect_subfmlas r [])) ys sj'''" "length ys = length ((vs @ [v]) @ rho)"
      using 2(7)
      by fastforce
    obtain t_split where t_split: "reach_sub ru_t l_t0 (map fst vs) t_split"
      "ru_t t_split = Some (Some (e', t), fst v)"
      using reach_sub_split_last[OF reach_sub_r_l_t0]
      by auto
    obtain t_e where t_split_def: "t_split = Some (t_e, fst v)"
      using t_split(2)
      by (cases t_split) (auto split: option.splits)
    have reach_sub_r_l_t0': "reach_sub ru_t l_t0 (map fst vs @ map fst (v # rho)) (Some (g', g_t))"
      using 2(6)
      by auto
    have fst_v_t: "fst v \<le> t"
      using ru_t_event[OF t_split(1) refl t_split(2)] ru_t_event[OF 2(5) refl, of _ t]
      unfolding t_split_def
      by (cases "ru_t (Some (e', t))") (fastforce split: option.splits)+
    have not_ets_gt: "\<not>g_t \<le> (fst v) + right I"
      using 2(8) fst_v_t add_mono[of _ _ "right I"] order.trans
      by (metis add.commute)
    obtain ws cv where ws_def: "reach_sub (ru (Suc n)) (su (Suc n) (MatchF I r)) ws cv"
      "length ws = length vs" "ru (Suc n) cv \<noteq> None"
      using 2(3)[OF 2(4) t_split(1)[unfolded t_split_def] reach_sub_r_l_t0' _ not_ets_gt] 2(7)
      by auto
    obtain w xs ctb where cv_def:
      "cv = VYDRA (Some (VYDRA_MatchF I (iarray_of_list transs) qf w, ctb))"
      "valid_matchF I l_t0 l_sub xs (Suc (length vs)) w"
      apply (rule wf_vydra.cases[OF vydra_wf[OF MatchF(1) ws_def(1) MatchF(9)]])
      using ws_def(2,3)
      by (auto simp: l_sub_def qf_def transs_def args')
    have cij_def: "w_i w = Suc (length vs)" "w_j w = length xs"
      using cv_def(2)
      by (auto simp: valid_window_matchF_def)
    have reach_cti: "reach_sub ru_t l_t0 (take (Suc (length vs)) (map fst xs)) (w_ti w)"
      "reach_sub ru_t (w_ti w) (drop (Suc (length vs)) (map fst xs)) (w_tj w)"
      "w_ti w = Some (e', t)"
      using cv_def(2) reach_sub_inj[OF _ 2(5)]
      by (auto simp: valid_window_matchF_def run_args)
    have read_cti: "read_t (w_ti w) = Some t"
      unfolding reach_cti
      by auto
    have reach_ctj: "reach_sub ru_t l_t0 (map fst xs) (w_tj w)"
      using cv_def(2) reach_sub_trans
      by (fastforce simp: valid_window_matchF_def run_args)
    have reach_csj: "reach_sub (run_subs (ru n)) (map (su n) (collect_subfmlas r []))
      (map snd xs) (w_sj w)"
      using cv_def(2) reach_sub_trans
      by (fastforce simp: valid_window_matchF_def run_args l_sub_def)
    have len_xs: "length xs \<le> length (vs @ v # rho)"
    proof (rule ccontr)
      assume contr: "\<not>length xs \<le> length (vs @ v # rho)"
      have ci_lt_cj: "w_i w < w_j w"
        using contr
        unfolding cij_def
        by auto
      have ts_at_xs_ci: "ts_at xs (w_i w) = t"
        apply (rule reach_sub.cases[OF reach_cti(2)[unfolded cij_def]])
        using contr nth_via_drop
        unfolding cij_def reach_cti
        by (fastforce simp: ts_at_def split: option.splits)+
      have reach_r_t_g_ctj: "reach_sub ru_t (Some (g', g_t))
        (drop (length (vs @ v # rho)) (map fst xs)) (w_tj w)"
        using reach_sub_split'[OF reach_ctj, of "length (vs @ v # rho)"] contr
          reach_sub_inj[OF 2(6)]
        by auto
      have ts_at_xs_gi: "ts_at xs (length (vs @ v # rho)) = g_t"
        apply (rule reach_sub.cases[OF reach_r_t_g_ctj])
        using contr nth_via_drop
        by (fastforce simp: ts_at_def split: option.splits)+
      show False
        using ts_at_xs_ci ts_at_xs_gi 2(8) cij_def contr cv_def(2)
        by (auto simp: valid_window_matchF_def)
    qed
    define rho' where "rho' = zip (drop (length xs) (map fst (vs @ [v]) @ map fst rho))
      (drop (length xs) ys)"
    have "reach_sub ru_t (w_tj w) (drop (length xs) (map fst (vs @ [v]) @ map fst rho))
      (Some (g', g_t))"
      using len_xs reach_sub_split'[OF 2(6), of "length xs"] reach_sub_inj[OF reach_ctj]
      by auto
    then have reach_ctj_rho': "reach_sub ru_t (w_tj w) (map fst rho') (Some (g', g_t))"
      using len_xs ys_def(2)
      unfolding rho'_def
      by auto
    have "reach_sub (run_subs (ru n)) (w_sj w) (drop (length xs) ys) sj'''"
      using len_xs reach_sub_split'[OF ys_def(1), of "length xs"] ys_def(2)
        reach_sub_inj[OF reach_csj]
      by auto
    then have reach_sub_csj_rho': "reach_sub (run_subs (ru n)) (w_sj w) (map snd rho') sj'''"
      using len_xs ys_def(2)
      unfolding rho'_def
      by auto
    have read_g: "read_t (Some (g', g_t)) = Some g_t"
      by auto
    have eval_not_None: "eval_mF I w \<noteq> None"
      using valid_eval_matchF_complete[OF cv_def(2)[unfolded l_sub_def], unfolded run_args, OF
        reach_ctj_rho' reach_sub_csj_rho' read_cti read_g 2(8)]
      by auto
    then obtain w' tb' where w'_def: "ru (Suc n) cv = Some (VYDRA (Some (w', tb')), ctb)"
      unfolding cv_def
      by (auto simp: qf_def transs_def args')
    have "ru (Suc n) (VYDRA (Some (w', tb'))) \<noteq> None"
      using vydra_wf[OF _ reach_sub_app[OF ws_def(1) w'_def] MatchF(9)]
      by auto
    then show ?case
      using reach_sub_app[OF ws_def(1) w'_def] ws_def(2)
      by fastforce
  qed
next
  case (Prev n I phi)
  have sub_prev: "su n (Prev I phi) = su n (PossiblyP phi I Wild)"
    by (auto simp: PossiblyP_def)
  have prems: "\<not>t' \<le> t + FR_fmla (PossiblyP phi I Wild)"
    "bounded_future_fmla (PossiblyP phi I Wild)"
    using Prev(7,8)
    by (auto simp: PossiblyP_def FR_pos(1) add_mono order.trans)
  show ?case
    using Prev(1)[OF Prev(2,3,4,5,6) prems]
    unfolding sub_prev .
next
  case (Next n I phi)
  have sub_next: "su n (Next I phi) = su n (PossiblyF Wild I phi)"
    by (auto simp: PossiblyF_def)
  have prems: "\<not>t' \<le> t + FR_fmla (PossiblyF Wild I phi)"
    "bounded_future_fmla (PossiblyF Wild I phi)"
    using Next(7,8)
    by (auto simp: PossiblyF_def FR_pos(1) sup_absorb2)
  show ?case
    using Next(1)[OF Next(2,3,4,5,6) prems]
    unfolding sub_next .
next
  case (Since n I phi psi)
  have sub_since: "su n (Since phi I psi) = su n (PossiblyP psi I (Star (BaseP phi)))"
    by (auto simp: PossiblyP_def BaseP_def)
  have prems: "\<not>t' \<le> t + FR_fmla (PossiblyP psi I (Star (BaseP phi)))"
    "bounded_future_fmla (PossiblyP psi I (Star (BaseP phi)))"
    using Since(7,8)
    by (auto simp: PossiblyP_def BaseP_def) (metis FR_pos(1) sup.commute sup.order_iff)
  show ?case
    using Since(1)[OF Since(2,3,4,5,6) prems]
    unfolding sub_since .
next
  case (Until n I phi psi)
  have sub_until: "su n (Until phi I psi) = su n (PossiblyF (Star (BaseF phi)) I psi)"
    by (auto simp: PossiblyF_def BaseF_def)
  have prems: "\<not>t' \<le> t + FR_fmla (PossiblyF (Star (BaseF phi)) I psi)"
    "bounded_future_fmla (PossiblyF (Star (BaseF phi)) I psi)"
    using Until(7,8)
    by (auto simp: PossiblyF_def BaseF_def) (metis FR_pos(1) sup.orderE)
  show ?case
    using Until(1)[OF Until(2,3,4,5,6) prems]
    unfolding sub_until .
qed

definition "ru' \<phi> = ru (msize_fmla \<phi>)"
definition "su' \<phi> = su (msize_fmla \<phi>) \<phi>"

lemma vydra_sound:
  assumes "reaches (ru' \<phi>) (su' \<phi>) n v" "ru' \<phi> v = Some (v', (t, b))" "bounded_future_fmla \<phi>"
  shows "t = \<tau> \<sigma> n \<and> b = sat n \<phi>"
  using vydra_wf[OF order.refl] reaches_sub[OF assms(1)] assms(2,3)
  by (auto simp: ru'_def su'_def dest: wf_vydraD)

lemma vydra_complete:
  assumes prefix: "reaches run_event init n e" "run_event e = Some (e', (t, X))"
    and prefix': "reaches run_event e n' f" "run_event f = Some (f', (t', X'))"
    and reach: "\<not>t' \<le> t + FR_fmla \<phi>" "bounded_future_fmla \<phi>"
  shows "\<exists>v v'. reaches (ru' \<phi>) (su' \<phi>) n v \<and> ru' \<phi> v = Some (v', (\<tau> \<sigma> n, sat n \<phi>))"
proof -
  obtain ws v where ws_def: "reach_sub (ru' \<phi>) (su' \<phi>) ws v" "length ws = n" "ru' \<phi> v \<noteq> None"
    using vydra_complete_sub[OF _ assms(2) _ assms(4) refl reach] reaches_sub[OF assms(1)]
      reaches_sub[OF assms(3)]
    unfolding ru'_def su'_def
    by blast
  obtain v' t b where tb_def: "ru' \<phi> v = Some (v', (t, b))"
    using ws_def(3)
    by auto
  show ?thesis
    using reach_sub_n[OF ws_def(1)] ws_def(2) tb_def
      wf_vydraD[OF vydra_wf[OF order.refl ws_def(1)[unfolded ru'_def su'_def] reach(2)]]
    by (auto simp: ru'_def)
qed

thm vydra_sound
thm vydra_complete

end

context MDL
begin

lemma reach_elem: "reach_sub (\<lambda>i. Some (Suc i, \<tau> \<sigma> i, \<Gamma> \<sigma> i)) s es s' \<Longrightarrow> s = 0 \<Longrightarrow> s' = length es"
  by (induction s es s' rule: reach_sub_rev_induct) auto

interpretation VYDRA_MDL \<sigma> 0 "\<lambda>i. Some (Suc i, (\<tau> \<sigma> i, \<Gamma> \<sigma> i))"
  using reach_elem
  by unfold_locales auto

end

end