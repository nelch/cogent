theory Subtyping
  imports Cogent
begin

text \<open>
  This file covers the interpretation of the subtyping relation as a lattice. This is how the
  compiler computes subtyping (as of late 2018), and these proofs give assurance we've formalised
  the correct relation.
\<close>

inductive type_lub :: "kind env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<leftarrow> _ \<squnion> _" [60,0,0,60] 60)
  and type_glb :: "kind env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<leftarrow> _ \<sqinter> _" [60,0,0,60] 60)
  where
  lub_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVar n \<leftarrow> TVar n1 \<squnion> TVar n2"
| lub_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<squnion> TVarBang n2"
| lub_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<squnion> TCon n2 ts2 s2"
| lub_tfun   : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; K \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<squnion> TFun t2 u2"
| lub_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TPrim p \<leftarrow> TPrim p1 \<squnion> TPrim p2"
| lub_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          if (K \<turnstile> fst (snd p1) :\<kappa> {D}) \<and> (K \<turnstile> fst (snd p2) :\<kappa> {D})
                                          then b = sup b1 b2
                                          else b = b1 \<and> b1 = b2) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
| lub_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; K \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<squnion> TProduct t2 u2"
| lub_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = sup (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
| lub_tunit  : "K \<turnstile> TUnit \<leftarrow> TUnit \<squnion> TUnit"

| glb_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVar n \<leftarrow> TVar n1 \<sqinter> TVar n2"
| glb_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<sqinter> TVarBang n2"
| glb_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<sqinter> TCon n2 ts2 s2"
| glb_tfun   : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; K \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<sqinter> TFun t2 u2"
| glb_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TPrim p \<leftarrow> TPrim p1 \<sqinter> TPrim p2"
| glb_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          if (K \<turnstile> fst (snd p1) :\<kappa> {D}) \<and> (K \<turnstile> fst (snd p2) :\<kappa> {D})
                                          then b = inf b1 b2
                                          else b = b1 \<and> b1 = b2) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
| glb_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; K \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<sqinter> TProduct t2 u2"
| glb_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = inf (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
| glb_tunit  : "K \<turnstile> TUnit \<leftarrow> TUnit \<sqinter> TUnit"

(*
(* This should not be true *)
lemma test5:
"\<And>i. i < length ts \<Longrightarrow> {D} \<subseteq> kinding_fn K (TSum ts) \<Longrightarrow> {D} \<subseteq> kinding_fn K (fst (snd (ts ! i)))"
  apply (drule_tac xs=ts and P="\<lambda>x. D \<in> (case x of (uu_, t, Checked) \<Rightarrow> UNIV | (uu_, t, Unchecked) \<Rightarrow> kinding_fn K t)" in  List.list_ball_nth)
   apply simp
  apply simp
  apply (subgoal_tac "\<exists>a b c. ts ! i = (a, b, c)")
   apply (erule exE)+
   apply simp
   apply (case_tac "c = Unchecked")
    apply simp
   apply (subgoal_tac "c = Checked")
    apply simp

  sorry

(* This should not be true *)
lemma test:
"K \<turnstile> TSum ts :\<kappa> {D} \<Longrightarrow> \<forall>i < length ts. K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
  apply (rule allI)
  apply (rule impI)
  apply (unfold kinding_def)
  apply (rule conjI)
  using test2 apply auto[1]
  apply (erule conjE) 
  apply simp thm List.list_ball_nth
  apply (drule_tac xs=ts and P="\<lambda>x. D \<in> (case x of (uu_, t, Checked) \<Rightarrow> UNIV | (uu_, t, Unchecked) \<Rightarrow> kinding_fn K t)" in  List.list_ball_nth)
   apply simp
  
  sorry
*)

lemma type_lub_type_glb_idem:
  assumes "K \<turnstile> t wellformed"
  shows
    "K \<turnstile> t \<leftarrow> t \<squnion> t"
    "K \<turnstile> t \<leftarrow> t \<sqinter> t"
  using assms
proof (induct t)
  case (TSum ts)
  moreover assume ts_wellformed: "K \<turnstile> TSum ts wellformed"
  ultimately show
    "K \<turnstile> TSum ts \<leftarrow> TSum ts \<squnion> TSum ts"
    "K \<turnstile> TSum ts \<leftarrow> TSum ts \<sqinter> TSum ts"
    by (fastforce simp add: list_all3_same list_all_iff intro!: type_lub_type_glb.intros)+
next
  case (TRecord ts s)
  moreover assume ts_wellformed: "K \<turnstile> TRecord ts s wellformed"
  ultimately show
  "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
  "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
     apply -
     apply (rule_tac lub_trecord)
           apply (metis (no_types, lifting) fsts.intros wellformed_record_wellformed_elem list_all3_same snds.intros surjective_pairing)
          apply (simp add: list_all3_same)
         apply (simp+)[5]
    apply (rule_tac glb_trecord)
          apply (metis (no_types, lifting) fsts.intros wellformed_record_wellformed_elem list_all3_same snds.intros surjective_pairing)
         apply (simp add: list_all3_same)
    by (simp+)[5]
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_commut:
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<squnion> a"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<sqinter> a"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
    apply (intro type_lub_type_glb.intros)
          apply (clarsimp simp add: list_all3_conv_all_nth)
         apply (clarsimp simp add: list_all3_conv_all_nth, metis sup_commute)
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
    done
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
    by (simp add: list_all3_conv_all_nth sup_commute type_lub_type_glb.lub_tsum)
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
    apply (intro type_lub_type_glb.intros)
          apply (clarsimp simp add: list_all3_conv_all_nth)
         apply (clarsimp simp add: list_all3_conv_all_nth, metis inf_commute)
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
    done
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
    by (simp add: inf_sup_aci(1) list_all3_conv_all_nth type_lub_type_glb.glb_tsum)
qed (fastforce intro!: type_lub_type_glb.intros)+


lemma type_lub_type_glb_wellformed:
  assumes
    "K \<turnstile> t1 wellformed"
    "K \<turnstile> t2 wellformed"
  shows
    "K \<turnstile> t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> K \<turnstile> t wellformed"
    "K \<turnstile> t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> K \<turnstile> t wellformed"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
qed (auto simp add: list_all_length list_all3_conv_all_nth)

lemma type_lub_type_glb_drop_impl_drop:
  assumes 
    "K \<turnstile> a :\<kappa> {D} \<or> K \<turnstile> b :\<kappa> {D}"
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
  case (glb_tsum K ts ts1 ts2)
  then show ?case
    apply (simp add: kinding_simps kinding_variant_conv_all_nth)
    apply (clarsimp simp add: list_all3_conv_all_nth)
    apply (erule_tac x=i in allE, erule impE, simp)+
    apply (case_tac "snd (snd (ts1 ! i)) = Checked")
     apply (case_tac "snd (snd (ts2 ! i)) = Checked")
      apply (metis inf_variant_state.simps(1) type_lub_type_glb_wellformed(2) variant_state.simps(3))
     apply (subgoal_tac "snd (snd (ts2 ! i)) = Unchecked")
      apply (simp, meson kinding_defs(1) type_lub_type_glb_wellformed(2) type_wellformed_pretty_def)
     apply (blast intro: variant_state.exhaust)
    apply (subgoal_tac "snd (snd (ts1 ! i)) = Unchecked")
     apply (case_tac "snd (snd (ts2 ! i)) = Checked")
      apply (simp, meson kinding_defs(1) type_lub_type_glb_wellformed(2) type_wellformed_pretty_def)
     apply (case_tac "snd (snd (ts2 ! i)) = Unchecked")
      apply (simp, blast intro: variant_state.exhaust)
    apply (blast intro: variant_state.exhaust)
    done
next
  case (lub_tfun K t t1 t2 u u1 u2)
  then show ?case 
    by (meson kinding_simps(4) type_lub_type_glb_wellformed(1) type_lub_type_glb_wellformed(2))
next
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case 
    apply (simp add: kinding_simps kinding_record_conv_all_nth)
    apply (clarsimp simp add: list_all3_conv_all_nth)
    apply (erule_tac x=i in allE, erule impE, simp)+
    apply (case_tac "snd (snd (ts1 ! i)) = Taken")
     apply (case_tac "snd (snd (ts2 ! i)) = Taken")
      apply (metis record_state.simps(3) sup_record_state.simps(1) type_lub_type_glb_wellformed(1))
     apply (metis kinding_to_wellformedD(1) record_state.simps(3) sup_record_state.simps(1))
    apply (subgoal_tac "snd (snd (ts1 ! i)) = Present")
     apply (case_tac "snd (snd (ts2 ! i)) = Taken")
      apply (metis bot_record_state_def kinding_to_wellformedD(1) record_state.simps(3) sup_bot.left_neutral)
     apply (subgoal_tac "snd (snd (ts2 ! i )) = Present")
      apply simp
     apply (blast intro: record_state.exhaust)
    apply (blast intro: record_state.exhaust)
    done
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case 
    apply (simp add: kinding_simps kinding_variant_conv_all_nth)
    apply (clarsimp simp add: list_all3_conv_all_nth)
    apply (erule_tac x=i in allE, erule impE, simp)+
    apply (case_tac "snd (snd (ts1 ! i)) = Unchecked")
     apply (case_tac "snd (snd (ts2 ! i)) = Checked")
      apply simp
      apply (simp add: kinding_def)
      apply (rule conjI)
       apply (meson kinding_defs(1) type_lub_type_glb_wellformed(1) type_wellformed_pretty_def)
      apply (erule conjE)+
    using lub_tsum.hyps(1)
      apply -
      apply (simp add: list_all3_conv_all_nth)
thm lub_tsum
    
   (*
    apply (case_tac "snd (snd (ts1 ! i)) = Checked")
     apply (case_tac "snd (snd (ts2 ! i)) = Checked")
      apply (metis sup_variant_state.simps(3) type_lub_type_glb_wellformed(1) variant_state.simps(3))
     apply (subgoal_tac "snd (snd (ts2 ! i)) = Unchecked")
      apply (erule conjE)
      apply (simp add: kinding_def)
      apply (rule conjI)
       apply (meson kinding_defs(1) type_lub_type_glb_wellformed(1) type_wellformed_pretty_def)
      apply (erule conjE)
      apply (erule impE)
    
      apply (subgoal_tac "snd (snd (ts1 ! i )) = Unchecked")
       apply (case_tac "snd (snd (ts2 ! i)) = Checked")
        apply simp
 *)
    sorry
next
  case (lub_tunit K)
  then show ?case sorry
next
  case (glb_tvar n n1 n2 K)
then show ?case sorry
next
  case (glb_tvarb n n1 n2 K)
  then show ?case sorry
next
  case (glb_tcon n n1 n2 s s1 s2 ts ts1 ts2 K)
  then show ?case sorry
next
  case (glb_tfun K t t1 t2 u u1 u2)
  then show ?case sorry
next
case (glb_tprim p p1 p2 K)
  then show ?case sorry
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case sorry
  (*
  proof (simp add: kinding_simps kinding_record_conv_all_nth)
    have " D \<in> sigil_kind s2"
      using assms glb_trecord.hyps
      sledgehammer
    show "(\<forall>i<length ts. case snd (snd (ts ! i)) of Taken \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed | Present \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}) \<and> D \<in> sigil_kind s2"
      sorry
  qed

    apply (simp add: kinding_simps kinding_record_conv_all_nth)
    apply (rule conjI)
     prefer 2
    using assms
    apply -
     apply (rule allI, rule impI)
     apply (case_tac "snd (snd (ts ! i)) = Taken")
      apply (clarsimp simp add: list_all3_conv_all_nth)
    using kinding_to_wellformedD(1) type_wellformed_pretty_def apply blast
     apply (case_tac "snd (snd (ts ! i)) = Present")
      apply (clarsimp simp add: list_all3_conv_all_nth)
    using sup_record_state.elims apply blast
  proof (simp add: kinding_simps kinding_record_conv_all_nth)
  *)
    sorry
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
  proof (simp add: kinding_simps kinding_variant_conv_all_nth)
    have "\<And>i. i < length ts \<Longrightarrow> snd (snd (ts ! i)) = Checked \<Longrightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed"
      apply simp
      using glb_tsum.hyps(1)
      apply -
      apply (clarsimp simp add: list_all3_conv_all_nth)
      

show "\<forall>i<length ts. case snd (snd (ts ! i)) of Checked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
  sorry
qed
  (*
    have "\<And>i. i < length ts \<Longrightarrow> snd (snd (ts ! i)) = Unchecked \<or> snd (snd (ts ! i)) = Checked"
      using variant_state.exhaust by blast
    moreover have "\<And>i. i < length ts \<Longrightarrow> snd (snd (ts ! i)) = Checked \<Longrightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed"
      sledgehammer
      by (metis (no_types, lifting) glb_tsum.hyps(1) kinding_iff_wellformed(1) list_all3_conv_all_nth)
    moreover have "\<And>i. i < length ts \<Longrightarrow> snd (snd (ts ! i)) = Unchecked \<Longrightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
      by (metis (mono_tags, lifting) glb_tsum.hyps(1) list_all3_conv_all_nth)
    ultimately show "\<forall>i<length ts. case snd (snd (ts ! i)) of Checked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
      by force
*)
qed (simp add: kinding_simps)+

next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
(*
    apply -
    apply (clarsimp simp add: list_all3_conv_all_nth kinding_defs)
    apply (rule conjI)
     apply (simp add: list_all_length)
*)
    sorry
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
(*
    apply -
    apply (simp add: kinding_defs list_all_def list_all3_conv_all_nth)
    apply (erule conjE)+
    apply (rule conjI)
    apply (clarsimp simp add: List.in_listsp_conv_set)
    apply (case_tac "b = Checked")
     apply simp
    apply (case_tac "b = Unchecked")
     apply (simp, metis fst_conv in_set_conv_nth snd_conv)
    apply (blast intro: variant_state.exhaust)
*)
    sorry
qed (simp add: kinding_simps)+

lemma type_lub_type_glb_absorb:
  shows
    "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> a \<leftarrow> a \<sqinter> c"
    "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a \<leftarrow> a \<squnion> c"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
next
  case (lub_trecord ts ts1 ts2 s s1 s2)
(*
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_trecord.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<squnion> t2 \<and> t1 \<leftarrow> t1 \<sqinter> t) \<and> b = inf b1 b2"
      using lub_trecord.hyps by blast+
    then show "t1' \<leftarrow> t1 \<sqinter> t \<and> b1' = sup b1 b"
      using lub_trecord.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
*)
  show ?case
    sorry
next
  case (lub_tsum ts ts1 ts2)
(*
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_tsum.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<squnion> t2 \<and> t1 \<leftarrow> t1 \<sqinter> t) \<and> b = inf b1 b2"
      using lub_tsum.hyps by blast+
    then show "t1' \<leftarrow> t1 \<sqinter> t \<and> b1' = sup b1 b"
      using lub_tsum.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
next
  case (glb_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
*)
  show ?case
    sorry
next
  case (glb_trecord ts ts1 ts2 s s1 s2)
(*
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_trecord.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<sqinter> t2 \<and> t1 \<leftarrow> t1 \<squnion> t) \<and> b = sup b1 b2"
      using glb_trecord.hyps by blast+
    then show "t1' \<leftarrow> t1 \<squnion> t \<and> b1' = inf b1 b"
      using glb_trecord.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
*)
  show ?case
    sorry
next
  case (glb_tsum ts ts1 ts2)
(*
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_tsum.hyps assms1 
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<sqinter> t2 \<and> t1 \<leftarrow> t1 \<squnion> t) \<and> b = sup b1 b2"
      using glb_tsum.hyps by blast+
    then show "t1' \<leftarrow> t1 \<squnion> t \<and> b1' = inf b1 b"
      using glb_tsum.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
*)
  show ?case
    sorry
qed (force intro: type_lub_type_glb.intros)+


lemma type_lub_type_glb_order_correct: "K \<turnstile> a \<leftarrow> a \<squnion> b \<longleftrightarrow> K \<turnstile> b \<leftarrow> a \<sqinter> b"
  by (auto intro: type_lub_type_glb_absorb type_lub_type_glb_commut)

lemma glb_lub_subtyping_order_correct:
  shows
    "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> (K \<turnstile> c \<sqsubseteq> a) \<and> (K \<turnstile> c \<sqsubseteq> b)"
    "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> (K \<turnstile> a \<sqsubseteq> c) \<and> (K \<turnstile> b \<sqsubseteq> c)"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case
    by (auto intro!: subtyping.intros simp add: list_all3_conv_all_nth list_all2_conv_all_nth)
next
  case (lub_trecord ts ts1 ts2 s s1 s2)
(*
  moreover { fix n t b t1 b1
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
    moreover then obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t \<sqsubseteq> t1 \<and> b \<le> b1"
      using lub_trecord.hyps by fastforce
  }
  moreover { fix n t b t2 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t2, b2) \<in> set ts2"
    moreover then obtain t1 b1 where "(n, t1, b1) \<in> set ts1"
      using lub_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t \<sqsubseteq> t2 \<and> b \<le> b2"
      using lub_trecord.hyps by fastforce
  }
  moreover have
    "\<And>n t b. (n, t, b) \<in> set ts \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    "\<And>n t2 b2. (n, t2, b2) \<in> set ts2 \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    using lub_trecord.hyps
    by (metis (no_types, hide_lams) eq_fst_iff image_iff)+
  ultimately show ?case
    by (auto intro!: subtyping.intros simp add: image_iff Bex_def)
*)
  show ?case
    sorry
next
  case (lub_tsum ts ts1 ts2)
(*
  moreover { fix n t b t1 b1
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
    moreover then obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t \<sqsubseteq> t1 \<and> b \<le> b1"
      using lub_tsum.hyps by fastforce
  }
  moreover { fix n t b t2 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t2, b2) \<in> set ts2"
    moreover then obtain t1 b1 where "(n, t1, b1) \<in> set ts1"
      using lub_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t \<sqsubseteq> t2 \<and> b \<le> b2"
      using lub_tsum.hyps by fastforce
  }
  moreover have
    "\<And>n t b. (n, t, b) \<in> set ts \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    "\<And>n t2 b2. (n, t2, b2) \<in> set ts2 \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    using lub_tsum.hyps
    by (metis (no_types, hide_lams) eq_fst_iff image_iff)+
  ultimately show ?case
    by (auto intro!: subtyping.intros simp add: image_iff Bex_def)
*)
  show ?case
    sorry
next
  case (glb_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case
    by (auto intro!: subtyping.intros simp add: list_all3_conv_all_nth list_all2_conv_all_nth)
next
  case (glb_trecord ts ts1 ts2 s s1 s2)
(*
  moreover { fix n t b t1 b1
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
    moreover then obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t1 \<sqsubseteq> t \<and> b1 \<le> b"
      using glb_trecord.hyps by fastforce
  }
  moreover { fix n t b t2 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t2, b2) \<in> set ts2"
    moreover then obtain t1 b1 where "(n, t1, b1) \<in> set ts1"
      using glb_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t2 \<sqsubseteq> t \<and> b2 \<le> b"
      using glb_trecord.hyps by fastforce
  }
  moreover have
    "\<And>n t b. (n, t, b) \<in> set ts \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    "\<And>n t2 b2. (n, t2, b2) \<in> set ts2 \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    using glb_trecord.hyps
    by (metis (no_types, hide_lams) eq_fst_iff image_iff)+
  ultimately show ?case
    by (auto intro!: subtyping.intros simp add: image_iff Bex_def)
*)
  show ?case
    sorry
next
  case (glb_tsum ts ts1 ts2)
(*
  moreover { fix n t b t1 b1
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
    moreover then obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t1 \<sqsubseteq> t \<and> b1 \<le> b"
      using glb_tsum.hyps by fastforce
  }
  moreover { fix n t b t2 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t2, b2) \<in> set ts2"
    moreover then obtain t1 b1 where "(n, t1, b1) \<in> set ts1"
      using glb_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "K \<turnstile> t2 \<sqsubseteq> t \<and> b2 \<le> b"
      using glb_tsum.hyps by fastforce
  }
  moreover have
    "\<And>n t b. (n, t, b) \<in> set ts \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    "\<And>n t2 b2. (n, t2, b2) \<in> set ts2 \<Longrightarrow> \<exists>t1 b1. (n, t1, b1) \<in> set ts1"
    using glb_tsum.hyps
    by (metis (no_types, hide_lams) eq_fst_iff image_iff)+
  ultimately show ?case
    by (auto intro!: subtyping.intros simp add: image_iff Bex_def)
*)
  show ?case
    sorry
qed (auto intro!: subtyping.intros)


lemma type_lub_type_glb_to_subtyping:
  shows
    "K \<turnstile> a \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> a \<sqsubseteq> b"
    "K \<turnstile> b \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a \<sqsubseteq> b"
  using glb_lub_subtyping_order_correct
  by fast+

(* this would be nice:
theorem type_glb_type_lub_subtyping_equivalent:
  shows
    "a \<leftarrow> a \<squnion> b \<longleftrightarrow> a \<sqsubseteq> b"
    "b \<leftarrow> a \<sqinter> b \<longleftrightarrow> a \<sqsubseteq> b"
  sorry
*)

end