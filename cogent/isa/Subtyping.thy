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
value "sup Taken Present"
value "sup Checked Unchecked"
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
    "((K \<turnstile> a :\<kappa> {D}) \<and> (K \<turnstile> b wellformed)) \<or> ((K \<turnstile> b :\<kappa> {D}) \<and> (K \<turnstile> a wellformed))"
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tsum K ts ts1 ts2)
  then show ?case 
    apply (simp add: kinding_simps kinding_variant_conv_all_nth)
    apply (clarsimp simp add: list_all_length list_all3_conv_all_nth)
    apply (case_tac "snd (snd (ts ! i))"; case_tac "snd (snd (ts1 ! i))"; case_tac "snd (snd (ts2 ! i))"; clarsimp; erule disjE; auto)
    

    sorry
next
  case (lub_tfun K t t1 t2 u u1 u2)
  then show ?case 
    by (metis kinding_def kinding_fn.simps(4) kinding_simps(4) type_lub_type_glb_wellformed(1) type_lub_type_glb_wellformed(2))
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
     proof (simp add: kinding_simps kinding_record_conv_all_nth)
    have assms1:
    "(K \<turnstile> TRecord ts1 s1 wellformed) \<and> (K \<turnstile> TRecord ts2 s2 wellformed)"
      using kinding_to_wellformedD(1) glb_trecord.prems by blast
    have assms2:
    "(K \<turnstile> TRecord ts1 s1 :\<kappa> {D}) \<or> (K \<turnstile> TRecord ts2 s2 :\<kappa> {D})"
      using glb_trecord.prems by blast
    have assms3:
      "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter>  TRecord ts2 s2"
      by (metis (no_types, lifting) glb_trecord.hyps list_all3_mono type_lub_type_glb.glb_trecord)
     moreover {
      fix i :: nat 
      assume tsLength: "i < length ts"
      moreover obtain c t t1 t2 b b1 b2 where dummy:
        "(c, t, b) = (ts ! i)" 
        "(c, t1, b1) = (ts1 ! i)"
        "(c, t2, b2) = (ts2 ! i)"
        by (metis (no_types, hide_lams) length_map glb_trecord.hyps(3) glb_trecord.hyps(4) nth_map surjective_pairing tsLength)
      have tsWellformed: "K \<turnstile> TRecord ts s wellformed"
        using assms1 assms3 type_lub_type_glb_wellformed(2) by blast
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy(1) nth_mem tsLength tsWellformed wellformed_record_wellformed_elem)
      have RecordExhaust: "(b = Taken \<or> b = Present) \<and> (b1 = Taken \<or> b1 = Present) \<and> (b2 = Taken \<or> b2 = Present)"
        using record_state.exhaust by blast
      have PresentIff: "(b = Taken) \<longleftrightarrow> (b1 = Taken) \<and> (b2 = Taken)"
        using glb_trecord.hyps(2)
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis RecordExhaust dummy inf_commute inf_record_state.simps(2) inf_record_state.simps(3) inf_sup_absorb snd_conv sup_record_state.simps(3) tsLength)
      have "type_wellformed (length K) t1"
        by (metis assms1 dummy(2) length_map glb_trecord.hyps(3) nth_mem tsLength type_wellformed_pretty_def wellformed_record_wellformed_elem)
      moreover have "type_wellformed (length K) t2"
        by (metis assms1 dummy(3) length_map glb_trecord.hyps(3) glb_trecord.hyps(4) nth_mem tsLength type_wellformed_pretty_def wellformed_record_wellformed_elem)
      moreover {
        assume "K \<turnstile> TRecord ts1 s1 :\<kappa> {D}"
        moreover have "b1 = Present \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
          using kinding_simps kinding_record_conv_all_nth
          by (metis calculation dummy(2) eq_snd_iff fst_conv length_map glb_trecord.hyps(3) record_state.simps(4) tsLength)
        moreover have  "(K \<turnstile> t1 :\<kappa> {D}) \<and> (type_wellformed (length K) t2) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using glb_trecord.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy fst_conv snd_conv tsLength)
        moreover have "b1 = Taken \<Longrightarrow> b2 = Taken \<Longrightarrow>  K \<turnstile> t wellformed"
          using tWellformed by blast
        moreover have "(K \<turnstile> t1 :\<kappa> {D}) \<and> (K \<turnstile> t2 :\<kappa> {D})  \<Longrightarrow>  b = inf b1 b2"
      }
  qed
  sorry
next
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case 
  proof -
    have assms1:
    "(K \<turnstile> TRecord ts1 s1 wellformed) \<and> (K \<turnstile> TRecord ts2 s2 wellformed)"
      using kinding_to_wellformedD(1) lub_trecord.prems by blast
    have assms2:
    "(K \<turnstile> TRecord ts1 s1 :\<kappa> {D}) \<or> (K \<turnstile> TRecord ts2 s2 :\<kappa> {D})"
      using lub_trecord.prems by blast
    have assms3:
      "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
      by (metis (no_types, lifting) list_all3_mono lub_trecord.hyps type_lub_type_glb.lub_trecord)
     moreover {
      fix i :: nat 
      assume tsLength: "i < length ts"
      moreover obtain c t t1 t2 b b1 b2 where dummy:
        "(c, t, b) = (ts ! i)" 
        "(c, t1, b1) = (ts1 ! i)"
        "(c, t2, b2) = (ts2 ! i)"
        by (metis (no_types, hide_lams) length_map lub_trecord.hyps(3) lub_trecord.hyps(4) nth_map surjective_pairing tsLength)
      have tsWellformed: "K \<turnstile> TRecord ts s wellformed"
        using assms1 assms3 type_lub_type_glb_wellformed(1) by blast
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy(1) nth_mem tsLength tsWellformed wellformed_record_wellformed_elem)
      have RecordExhaust: "(b = Taken \<or> b = Present) \<and> (b1 = Taken \<or> b1 = Present) \<and> (b2 = Taken \<or> b2 = Present)"
        using record_state.exhaust by blast
      have PresentIff: "(b = Present) \<longleftrightarrow> (b1 = Present) \<and> (b2 = Present)"
        using lub_trecord.hyps(2)
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis (no_types, lifting) RecordExhaust dummy snd_conv sup.right_idem sup_commute sup_record_state.simps(2) sup_record_state.simps(3) tsLength)
      have "type_wellformed (length K) t1"
        by (metis assms1 dummy(2) length_map lub_trecord.hyps(3) nth_mem tsLength type_wellformed_pretty_def wellformed_record_wellformed_elem)
      moreover have "type_wellformed (length K) t2"
        by (metis assms1 dummy(3) length_map lub_trecord.hyps(3) lub_trecord.hyps(4) nth_mem tsLength type_wellformed_pretty_def wellformed_record_wellformed_elem)
      moreover {
        assume "K \<turnstile> TRecord ts1 s1 :\<kappa> {D}"
        moreover have "b1 = Present \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
          using kinding_simps kinding_record_conv_all_nth
          by (metis calculation dummy(2) eq_snd_iff fst_conv length_map lub_trecord.hyps(3) record_state.simps(4) tsLength)
        moreover have  "(K \<turnstile> t1 :\<kappa> {D}) \<and> (type_wellformed (length K) t2) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using lub_trecord.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy fst_conv snd_conv tsLength)
        moreover have "b1 = Present \<Longrightarrow> b2 = Present \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
          by (simp add: \<open>type_wellformed (length K) t2\<close> calculation(2) calculation(3))
        ultimately have "case b of Taken \<Rightarrow> K \<turnstile> t wellformed | Present \<Rightarrow> K \<turnstile> t :\<kappa> {D}"
          using RecordExhaust PresentIff tWellformed by auto
      }
      moreover {
        assume "K \<turnstile> TRecord ts2 s2 :\<kappa> {D}"
        moreover have "b2 = Present \<Longrightarrow> K \<turnstile> t2 :\<kappa> {D}"
          using kinding_simps kinding_variant_conv_all_nth
          by (metis calculation dummy(3) eq_snd_iff fst_conv kinding_record_conv_all_nth length_map lub_trecord.hyps(3) lub_trecord.hyps(4) record_state.simps(4) tsLength)
        moreover have  "(K \<turnstile> t2 :\<kappa> {D}) \<and> (type_wellformed (length K) t1) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using lub_trecord.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy fst_conv snd_conv tsLength)
        moreover have "b1 = Present \<Longrightarrow> b2 = Present \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using \<open>type_wellformed (length K) t1\<close> calculation(2) calculation(3) by blast
        ultimately have "case b of Taken \<Rightarrow> K \<turnstile> t wellformed | Present \<Rightarrow> K \<turnstile> t :\<kappa> {D}"
          using RecordExhaust PresentIff tWellformed by auto
      }
      moreover have "case snd (snd (ts ! i)) of Taken \<Rightarrow>  K \<turnstile> fst (snd (ts ! i)) wellformed | Present \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
        by (metis calculation(4) calculation(5) dummy(1) fst_conv lub_trecord.prems snd_conv)
    }
    ultimately show "K \<turnstile> TRecord ts s :\<kappa> {D}"
      using assms2 kinding_record_conv_all_nth kinding_simps(8) lub_trecord.hyps(5) lub_trecord.hyps(6) lub_trecord.hyps(7) by auto
  qed
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case 
  proof (simp add: kinding_simps kinding_variant_conv_all_nth)
    have assms1: 
      "(K \<turnstile> TSum ts1 wellformed) \<and> (K \<turnstile> TSum ts2 wellformed)"
      using kinding_to_wellformedD(1) lub_tsum.prems by blast
    have assms2:
      "(K \<turnstile> TSum ts1 :\<kappa> {D}) \<or> (K \<turnstile> TSum ts2 :\<kappa> {D})"
        using lub_tsum.prems kinding_defs(1) by blast
    have assms3:
      "K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
      by (metis (no_types, lifting) list_all3_mono lub_tsum.hyps type_lub_type_glb.lub_tsum)
    moreover {
      fix i :: nat 
      assume tsLength: "i < length ts"
      moreover obtain c t t1 t2 b b1 b2 where dummy:
        "(c, t, b) = (ts ! i)" 
        "(c, t1, b1) = (ts1 ! i)"
        "(c, t2, b2) = (ts2 ! i)"
        by (metis (no_types, hide_lams) calculation lub_tsum.hyps(3) lub_tsum.hyps(4) length_map nth_map prod.collapse)
      have tsWellformed: "K \<turnstile> TSum ts wellformed"
        using assms1 assms3 type_lub_type_glb_wellformed(1) by blast
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy(1) calculation nth_mem tsWellformed wellformed_sum_wellformed_elem)
      have VariantExhaust: "(b = Checked \<or> b = Unchecked) \<and> (b1 = Checked \<or> b1 = Unchecked) \<and> (b2 = Checked \<or> b2 = Unchecked)"
        using variant_state.exhaust by blast
      have UncheckedIff: "(b = Unchecked) \<longleftrightarrow> (b1 = Unchecked) \<or> (b2 = Unchecked)"
        using lub_tsum.hyps(2)
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis VariantExhaust bot_variant_state_def dummy inf_bot_right inf_sup_absorb snd_conv sup_bot.right_neutral sup_commute tsLength)
      have CheckedIff: "(b = Checked) \<longleftrightarrow> (b1 = Checked) \<and> (b2 = Checked)"
        using lub_tsum.hyps(2)
        apply (clarsimp simp add: list_all3_conv_all_nth)
        using UncheckedIff VariantExhaust by blast
      have t1Wellformed: "type_wellformed (length K) t1"
        by (metis assms1(1) dummy(2) lub_tsum.hyps(3) length_map nth_mem tsLength type_wellformed_pretty_def wellformed_sum_wellformed_elem)
      have t2Wellformed: "type_wellformed (length K) t2"
        by (metis assms1 dummy(3) lub_tsum.hyps(3) lub_tsum.hyps(4) length_map nth_mem tsLength type_wellformed_pretty_def wellformed_sum_wellformed_elem)
      have  "(K \<turnstile> t1 :\<kappa> {D}) \<and> (type_wellformed (length K) t2) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using lub_tsum.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy fst_conv snd_conv tsLength)
      have  "(K \<turnstile> t2 :\<kappa> {D}) \<and> (type_wellformed (length K) t1) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using lub_tsum.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy fst_conv snd_conv tsLength)
      moreover {
        assume "K \<turnstile> TSum ts1 :\<kappa> {D}"
        moreover have "b1 = Unchecked \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
          using kinding_simps kinding_variant_conv_all_nth
          by (metis calculation dummy(2) fst_conv length_map lub_tsum.hyps(3) snd_conv tsLength variant_state.simps(4))
        moreover have "b1 = Unchecked \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
          by (simp add: \<open>K \<turnstile> t1 :\<kappa> {D} \<and> type_wellformed (length K) t2 \<longrightarrow> K \<turnstile> t :\<kappa> {D}\<close> calculation(2) t2Wellformed)


(*
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
 *)*)
  qed
next
  case (glb_tfun K t t1 t2 u u1 u2)
  then show ?case
    by (metis kinding_def kinding_fn.simps(4) kinding_simps(4) type_lub_type_glb_wellformed(1) type_lub_type_glb_wellformed(2))
    sorry
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
  proof -
    have assms1: 
      "(K \<turnstile> TSum ts1 wellformed) \<and> (K \<turnstile> TSum ts2 wellformed)"
      using glb_tsum.prems kinding_defs(1) by blast
    have assms2:
      "(K \<turnstile> TSum ts1 :\<kappa> {D}) \<or> (K \<turnstile> TSum ts2 :\<kappa> {D})"
        using glb_tsum.prems kinding_defs(1) by blast
    have assms3:
      "K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
      by (metis (no_types, lifting) glb_tsum.hyps(1) glb_tsum.hyps(2) glb_tsum.hyps(3) glb_tsum.hyps(4) glb_tsum.hyps(5) list_all3_mono type_lub_type_glb.glb_tsum)
    moreover {
      fix i :: nat 
      assume tsLength: "i < length ts"
      moreover obtain c t t1 t2 b b1 b2 where dummy:
        "(c, t, b) = (ts ! i)" 
        "(c, t1, b1) = (ts1 ! i)"
        "(c, t2, b2) = (ts2 ! i)"
        by (metis (no_types, hide_lams) calculation glb_tsum.hyps(3) glb_tsum.hyps(4) length_map nth_map prod.collapse)
      have tsWellformed: "K \<turnstile> TSum ts wellformed"
        using assms1 assms3 type_lub_type_glb_wellformed(2) by blast
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy(1) calculation nth_mem tsWellformed wellformed_sum_wellformed_elem)
      have VariantExhaust: "(b = Checked \<or> b = Unchecked) \<and> (b1 = Checked \<or> b1 = Unchecked) \<and> (b2 = Checked \<or> b2 = Unchecked)"
        using variant_state.exhaust by blast
      have UncheckedIff: "(b = Unchecked) \<longleftrightarrow> (b1 = Unchecked) \<and> (b2 = Unchecked)"
        using glb_tsum.hyps(2)
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis (no_types, hide_lams) calculation dummy inf.right_idem inf_commute inf_top.left_neutral snd_conv top_variant_state_def)
      have "type_wellformed (length K) t1"
        by (metis assms1(1) dummy(2) glb_tsum.hyps(3) length_map nth_mem tsLength type_wellformed_pretty_def wellformed_sum_wellformed_elem)
      moreover have "type_wellformed (length K) t2"
        by (metis assms1 dummy(3) glb_tsum.hyps(3) glb_tsum.hyps(4) length_map nth_mem tsLength type_wellformed_pretty_def wellformed_sum_wellformed_elem)
      moreover {
        assume "K \<turnstile> TSum ts1 :\<kappa> {D}"
        moreover have "b1 = Unchecked \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
          using kinding_simps kinding_variant_conv_all_nth
          by (metis tsLength calculation dummy(2) fst_conv glb_tsum.hyps(3) length_map snd_conv variant_state.simps(4))
        moreover have  "(K \<turnstile> t1 :\<kappa> {D}) \<and> (type_wellformed (length K) t2) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using glb_tsum.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy(1) dummy(2) dummy(3) fst_conv snd_conv tsLength)
        moreover have "b1 = Unchecked \<Longrightarrow> b2 = Unchecked \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using \<open>type_wellformed (length K) t2\<close> calculation(2) calculation(3) by linarith
        ultimately have "case b of Checked \<Rightarrow> K \<turnstile> t wellformed | Unchecked \<Rightarrow> K \<turnstile> t :\<kappa> {D}"
          using VariantExhaust tWellformed UncheckedIff by auto
      }
      moreover {
        assume "K \<turnstile> TSum ts2 :\<kappa> {D}"
        moreover have "b2 = Unchecked \<Longrightarrow> K \<turnstile> t2 :\<kappa> {D}"
          using kinding_simps kinding_variant_conv_all_nth
          by (metis calculation dummy(3) fst_conv glb_tsum.hyps(3) glb_tsum.hyps(4) length_map snd_conv tsLength variant_state.simps(4))
        moreover have  "(K \<turnstile> t2 :\<kappa> {D}) \<and> (type_wellformed (length K) t1) \<longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using glb_tsum.hyps(1)
          apply (clarsimp simp add: list_all3_conv_all_nth)
          by (metis dummy(1) dummy(2) dummy(3) fst_conv snd_conv tsLength)
        moreover have "b1 = Unchecked \<Longrightarrow> b2 = Unchecked \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
          using \<open>type_wellformed (length K) t1\<close> calculation(2) calculation(3) by linarith
        ultimately have "case b of Checked \<Rightarrow> K \<turnstile> t wellformed | Unchecked \<Rightarrow> K \<turnstile> t :\<kappa> {D}"
          using UncheckedIff VariantExhaust tWellformed by auto
      }
      moreover have "case snd (snd (ts ! i)) of Checked \<Rightarrow>  K \<turnstile> fst (snd (ts ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
        by (metis assms2 calculation(4) calculation(5) dummy(1) fst_conv snd_conv)
    }
    ultimately show "K \<turnstile> TSum ts :\<kappa> {D}"
      by (simp add: glb_tsum.hyps(5) kinding_simps(6) kinding_variant_conv_all_nth)
  qed
qed (auto simp add: kinding_simps)+

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
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof (intro type_lub_type_glb.intros; clarsimp simp add: list_all3_conv_all_nth)
    fix i
    presume
      "let b = snd (snd (ts ! i)); b1 = snd (snd (ts1 ! i)); b2 = snd (snd (ts2 ! i))
        in if (K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}) \<and> (K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}) then b = sup b1 b2 else b = b1 \<and> b1 = b2"
      "K \<turnstile> fst (snd (ts ! i)) \<leftarrow> fst (snd (ts1 ! i)) \<squnion> fst (snd (ts2 ! i))"
      "K \<turnstile> fst (snd (ts1 ! i)) \<leftarrow> fst (snd (ts1 ! i)) \<sqinter> fst (snd (ts ! i))"
    then show "let b = snd (snd (ts1 ! i)); b2 = snd (snd (ts ! i))
              in (K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D} \<and> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D} \<longrightarrow> b = inf b b2) \<and>
                 ((K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D} \<longrightarrow> \<not> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}) \<longrightarrow> b = b2)"
      apply (case_tac "K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}";
          case_tac "K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}";
          case_tac "K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}"; clarsimp)
            apply (metis inf.idem)
           apply metis
          apply metis
         defer
         apply metis
        apply metis
       apply metis


      sorry
  qed auto
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
    by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof (intro type_lub_type_glb.intros; clarsimp simp add: list_all3_conv_all_nth)
    fix i
    presume
      "let b = snd (snd (ts ! i)); b1 = snd (snd (ts1 ! i)); b2 = snd (snd (ts2 ! i))
        in if (K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}) \<and> (K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}) then b = inf b1 b2 else b = b1 \<and> b1 = b2"
      "K \<turnstile> fst (snd (ts ! i)) \<leftarrow> fst (snd (ts1 ! i)) \<sqinter> fst (snd (ts2 ! i))"
      "K \<turnstile> fst (snd (ts1 ! i)) \<leftarrow> fst (snd (ts1 ! i)) \<squnion> fst (snd (ts ! i))"
    then show "let b = snd (snd (ts1 ! i)); b2 = snd (snd (ts ! i))
              in (K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D} \<and> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D} \<longrightarrow> b = sup b b2) \<and>
                 ((K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D} \<longrightarrow> \<not> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}) \<longrightarrow> b = b2)"
      apply (case_tac "K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}";
          case_tac "K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}";
          case_tac "K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}"; clarsimp)
             apply (metis sup.idem)
            apply metis
          apply metis
          defer
          apply metis
         apply metis
        apply metis
      sorry
  qed auto
next
  case (glb_tsum ts ts1 ts2)
  then show ?case
    by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
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
*)
end