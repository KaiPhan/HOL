(* ========================================================================= *)
(* The Central Limit Theorems                                                *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open pairTheory combinTheory optionTheory prim_recTheory arithmeticTheory
                pred_setTheory pred_setLib topologyTheory hurdUtils;

open realTheory realLib iterateTheory seqTheory transcTheory real_sigmaTheory
                real_topologyTheory;

open util_probTheory extrealTheory sigma_algebraTheory measureTheory
     real_borelTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory derivativeTheory extreal_baseTheory;

open distributionTheory;

open limTheory;

val _ = new_theory "central_limit";

Theorem liapounov_ineq_lemma:
    !m u p. measure_space m ∧
            measure m (m_space m) < PosInf ∧
            1 < p ∧ p < PosInf ∧
            u ∈ lp_space p m  ⇒
            ∫⁺ m (λx. abs (u x)) ≤ seminorm p m u * ((measure m (m_space m)) powr (1 - inv(p)))
Proof
    rpt STRIP_TAC
 >> ‘p ≠ PosInf’ by rw[lt_imp_ne]
 >> ‘0 < p’ by METIS_TAC [lt_trans, lt_01]
 >> ‘p ≠ 0’ by rw[lt_imp_ne]
 >> ‘inv(p) ≠ NegInf ∧ inv(p) ≠ PosInf’ by rw[inv_not_infty]
 >> ‘p ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘0 < inv (p)’ by METIS_TAC [inv_pos']
 >> ‘inv(p) ≠ 0’ by rw[lt_imp_ne]
 >> Know ‘inv (p) < 1’
 >- (‘1 * inv(p) < p * inv(p)’ by rw[lt_rmul] \\
     ‘p / p = p * inv(p)’ by rw [div_eq_mul_rinv] \\
     ‘p / p = 1’ by METIS_TAC [div_refl_pos] \\
     ‘inv(p) = 1 * inv(p)’ by rw[] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘0 < 1 - inv(p)’ by rw[sub_zero_lt]
 >> ‘1 - inv(p) ≠ 0’ by rw[lt_imp_ne]
 >> Know ‘1 - inv(p) ≠ NegInf’
 >- (‘∃a. inv(p) = Normal a’ by METIS_TAC [extreal_cases] \\
     ‘∃c. Normal 1 - Normal a = Normal c’ by METIS_TAC [extreal_sub_def] \\
     Know ‘1 - inv(p) = Normal c’
     >- (‘1 = Normal 1’ by rw[] >> rw[]) >> rw[])
 >> DISCH_TAC
 >> Know ‘1 - inv(p) ≠ PosInf’
 >- (‘∃b. inv(p) = Normal b’ by METIS_TAC [extreal_cases]
     >> ‘∃d. Normal 1 - Normal b = Normal d’ by METIS_TAC [extreal_sub_def]
     >> Know ‘1 - inv(p) = Normal d’
     >- (‘1 = Normal 1’ by rw[] >> rw[]) >> rw[])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘q = inv(1- inv(p))’
 >> Know ‘inv(p) + inv(q) = 1’
 >- (rw [Abbr ‘q’, inv_inv] \\
     rw [sub_add2, inv_not_infty])
 >> DISCH_TAC
 >> Know ‘0 < q’
 >- (Q.UNABBREV_TAC ‘q’ \\
     MATCH_MP_TAC inv_pos' \\
     CONJ_TAC (*  0 < 1 − p⁻¹ *)
     >- (MATCH_MP_TAC sub_zero_lt \\
         MP_TAC ( Q.SPECL [‘p’, ‘1’] inv_lt_antimono) \\
         simp[lt_01, inv_one]) \\
      (*  1 − p⁻¹ ≠ +∞ *)
    rw[])
 >> DISCH_TAC
 >> Know ‘q ≠ PosInf’
 >- (Q.UNABBREV_TAC ‘q’ \\
     rw[inv_not_infty])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘u’, ‘λx. 1’, ‘p’, ‘q’]
            Hoelder_inequality')
 >> impl_tac
 >> simp[]
 (* (λx. 1) ∈ lp_space q m*)
 >- (rw[lp_space_def]
 (*  (λx. 1) ∈ Borel_measurable (measurable_space m) *)
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' \\
         rw [measure_space_def])
    (* ∫⁺ m (λx. abs 1 powr q) ≠ +∞ *)
     >> ‘abs 1 = 1’ by rw[abs_refl]
     >> rw[]
     >> Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw[])
     >> DISCH_TAC
     >> simp[]
    (* ∫⁺ m (λx. 1) ≠ +∞ *)
     >> MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const)
     >> impl_tac
     >> simp[]
     >> DISCH_TAC
     >> ‘1 = Normal 1’ by rw[]
    (*  measure m (m_space m) <> +∞ *)
     >> rw[]
     >> ‘measure m (m_space m) ≠ +∞’ by rw[lt_imp_ne]
     >> rw [mul_not_infty])
 >> DISCH_TAC
 >> Know ‘seminorm q m (λx. 1) = ((measure m (m_space m)) powr (1 - inv(p)))’
 >- (rw[seminorm_def] \\
     Know ‘inv (q) = 1 - inv (p)’
     >- (Q.UNABBREV_TAC ‘q’ \\
         rw[inv_inv]) \\
     DISCH_TAC \\
     rw[] \\
    ‘abs 1 = 1’ by rw[abs_refl] \\
     rw[] \\
     Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw[]) \\
     DISCH_TAC  \\
    ‘1 = Normal 1’ by rw[] \\
     simp[] \\
     Know ‘∫⁺ m (λx. Normal 1) =  measure m (m_space m)’
     >- (MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const) \\
         impl_tac \\
         simp[] \\
        ‘1 * measure m (m_space m) =  measure m (m_space m) ’ by rw[mul_lone] \\
         simp[] \\
         DISCH_TAC \\
         METIS_TAC[]) \\
     DISCH_TAC \\
     simp[])
 >> DISCH_TAC
 >> METIS_TAC []
QED

Theorem liapounov_ineq:
    !m u r r'. measure_space m /\ u IN lp_space r m ∧  u IN lp_space r' m ∧
               measure m (m_space m) < PosInf ∧
               0 < r ∧
               r < r' ∧
               r' < PosInf  ==>
               seminorm r m u ≤ seminorm r' m u * (measure m (m_space m)) powr (inv(r) - inv(r'))
Proof
    rpt STRIP_TAC
 >> ‘0 < r'’ by METIS_TAC [lt_trans]
 >> ‘r < PosInf’ by METIS_TAC [lt_trans]
 >> ‘r ≠ 0 ∧ r' ≠ 0’ by rw [lt_imp_ne]
 >> ‘r ≠ PosInf ∧ r' ≠ PosInf ’ by rw[lt_imp_ne]
 >> ‘NegInf < r ∧ NegInf < r'’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘r ≠ NegInf ∧ r' ≠ NegInf’ by METIS_TAC [lt_imp_ne]
 >> Know ‘inv r <> PosInf /\ inv r <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> Know ‘inv r' <> PosInf /\ inv r' <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> ‘0 < inv (r) ∧ 0 < inv (r')’ by METIS_TAC [inv_pos']
 >> ‘inv(r) ≠ 0 ∧ inv(r') ≠ 0’ by rw [lt_imp_ne]
 >> ‘inv(r') * r ≠ NegInf ∧ inv(r') * r ≠ PosInf’ by METIS_TAC[mul_not_infty2]
 >>  ‘r' * inv(r) ≠ NegInf ∧ r' * inv(r) ≠ PosInf’ by METIS_TAC[mul_not_infty2]
 >> Know ‘1 < r' * r⁻¹’
 >- (‘r * inv(r) < r' * inv(r)’ by rw[lt_rmul] \\
     ‘r / r = r * inv(r)’ by rw [div_eq_mul_rinv] \\
     ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     METIS_TAC[])
 >> DISCH_TAC
 >> ‘0 < r' * inv(r)’ by METIS_TAC[lt_01, lt_trans]
 >> MP_TAC (Q.SPECL [‘m’, ‘λx. abs (u x) powr r’, ‘r'* inv(r)’]
            liapounov_ineq_lemma)
 >> impl_tac
 >> simp[]
 >- (CONJ_TAC
    (*  r' * r⁻¹ < +∞ *)
     >- (‘∃a. r' * inv(r) = Normal a’ by METIS_TAC [extreal_cases] \\
          rw[lt_infty])
    (* (λx. u x powr r) ∈ lp_space (r' * r⁻¹) m  *)
     >> gs [lp_space_alt_finite]
     >> CONJ_TAC
     >- (HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS_POWR \\
         CONJ_TAC
        (* u ∈ Borel_measurable (measurable_space m) *)
         >- (‘u IN measurable (m_space m,measurable_sets m) Borel’
                by gs [lp_space_def]) \\
        (* 0 ≤ r*)
         CONJ_TAC
         >- (MATCH_MP_TAC lt_imp_le \\
             rw[]) \\
        (* r ≠ +∞ *)
             simp[])
      (* ∫⁺ m (λx. abs (abs (u x) powr r) powr (r' * r⁻¹)) ≠ +∞ *)
      >> ‘∀x. abs (abs (u x) powr r) = abs (u x) powr r’ by rw [abs_pos, powr_pos, abs_refl]
      >> POP_ORW
      >> ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) = abs (u x) powr (r * (r' * r⁻¹))’ by rw[powr_powr]
      >> POP_ORW
      >> ‘r * (r' * r⁻¹) = r * inv(r) * r'’ by PROVE_TAC[mul_comm, mul_assoc]
      >> ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv]
      >> ‘r * inv(r) = inv(r) * r’ by PROVE_TAC[mul_comm]
      >> ‘r / r = 1’ by METIS_TAC [div_refl_pos]
      >> FULL_SIMP_TAC std_ss [mul_lone])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘mu =  measure m (m_space m)’
 >> Know ‘0 ≤ mu’
 >- (Q.UNABBREV_TAC ‘mu’ \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp[] \\
     METIS_TAC[MEASURE_SPACE_MSPACE_MEASURABLE])
 >> DISCH_TAC
 >> ‘∀x. abs (abs (u x) powr r) = abs (u x) powr r’ by rw [abs_pos, powr_pos, abs_refl]
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘seminorm (r' * r⁻¹) m (λx. abs (u x) powr r) = (seminorm r' m u) powr r’
 >- (rw[seminorm_def] \\
     ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) =  abs (u x) powr (r * (r' * r⁻¹))’ by rw[abs_pos, powr_powr] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r * (r' * r⁻¹)) = abs (u x) powr (r⁻¹ * r * r')’ by PROVE_TAC[mul_assoc, mul_comm] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r⁻¹ * r * r') = abs (u x) powr r'’ by rw[mul_linv_pos, mul_lone] \\
     POP_ORW \\
     ‘inv(r' * inv(r)) = inv(r') * r’ by rw[inv_mul, inv_inv] \\
     POP_ORW \\
     Know ‘0 ≤ ∫⁺ m (λx. abs (u x) powr r')’
     >- (MATCH_MP_TAC pos_fn_integral_pos \\
         simp[] \\
        (* ∀x. x ∈ m_space m ⇒ 0 ≤ abs (u x) powr r'*)
         METIS_TAC [abs_pos, powr_pos]) \\
     DISCH_TAC \\
     ‘∫⁺ m (λx. abs (u x) powr r') powr (r'⁻¹ * r) = (∫⁺ m (λx. abs (u x) powr r') powr r'⁻¹) powr r’
         by rw[GSYM powr_powr])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘A =  ∫⁺ m (λx. abs (u x) powr r)’
 >> Q.ABBREV_TAC ‘B =  seminorm r' m u powr r * mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp []
 >> Know ‘A powr inv(r) ≤ B powr inv(r)’
 >- (Know ‘0 ≤ A’
     >- (rw[Abbr ‘A’] \\
         MATCH_MP_TAC pos_fn_integral_pos \\
         simp[] \\
        (* ∀x. x ∈ m_space m ⇒ 0 ≤ abs (u x) powr r'*)
         METIS_TAC [abs_pos, powr_pos]) \\
     DISCH_TAC \\
     Know ‘0 ≤ B’
     >- (rw[Abbr ‘B’] \\
        ‘0 ≤ seminorm r' m u’ by PROVE_TAC [seminorm_pos] \\
        ‘0 ≤ seminorm r' m u powr r’ by PROVE_TAC [powr_pos] \\
        ‘0 ≤  mu powr (1 − (r' * r⁻¹)⁻¹)’ by PROVE_TAC [powr_pos] \\
         METIS_TAC [le_mul]) \\
     DISCH_TAC \\
     METIS_TAC [GSYM powr_mono_eq])
 >> DISCH_TAC
 >> Q.UNABBREV_TAC ‘A’
 >> Q.UNABBREV_TAC ‘B’
 >> ‘∫⁺ m (λx. abs (u x) powr r) powr inv(r) = seminorm r m u’ by rw[seminorm_def]
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘C = seminorm r' m u’
 >> Q.ABBREV_TAC ‘D = mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp[]
 >> Know ‘(C powr r * D) powr r⁻¹ = C * D powr inv(r)’
 >- (‘0 ≤ C’ by PROVE_TAC [seminorm_pos] \\
     ‘0 ≤ C powr r’ by PROVE_TAC [powr_pos] \\
     ‘0 ≤ D’ by METIS_TAC[powr_pos] \\
     ‘(C powr r * D) powr r⁻¹ = (C powr r) powr r⁻¹ * D powr inv(r)’ by  METIS_TAC[mul_powr] \\
     ‘(C powr r) powr r⁻¹ = C powr (r * inv(r))’ by METIS_TAC[powr_powr] \\
     ‘C powr (r * inv(r)) = C’ by METIS_TAC[GSYM div_eq_mul_rinv, div_refl_pos, powr_1] \\
      simp[])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.UNABBREV_TAC ‘C’
 >> Q.UNABBREV_TAC ‘D’
 >> Know ‘(mu powr (1 − (r' * r⁻¹)⁻¹)) powr r⁻¹ =
           mu powr (r⁻¹ − r'⁻¹)’
 >- (Know ‘r * inv(r') < 1’
     >- (‘r * inv(r') < r' * inv(r')’ by rw[lt_rmul] \\
         ‘r' / r' = r' * inv(r')’ by rw [div_eq_mul_rinv] \\
         ‘r' / r' = 1’ by METIS_TAC [div_refl_pos] \\
          METIS_TAC[]) \\
     DISCH_TAC \\
    ‘r * r'⁻¹ = r'⁻¹ * r’ by METIS_TAC[mul_comm] \\
     FULL_SIMP_TAC std_ss [] \\
    ‘(r' * r⁻¹)⁻¹ = inv(r') * r’ by METIS_TAC[inv_mul, inv_inv, mul_comm] \\
     simp[] \\
    ‘0 < 1 - inv(r') * r’ by METIS_TAC[sub_zero_lt] \\
     Know ‘1 − r'⁻¹ * r ≠ PosInf’
     >- (‘∃b. r'⁻¹ * r  = Normal b’ by METIS_TAC [extreal_cases] \\
          rw[sub_not_infty]) \\
     DISCH_TAC \\
    ‘(mu powr (1 − r'⁻¹ * r)) powr r⁻¹ = mu powr ((1 − r'⁻¹ * r) * inv(r))’
         by METIS_TAC [powr_powr] \\
     POP_ORW \\
    ‘(1 − r'⁻¹ * r) * r⁻¹ =  r⁻¹ * (1 − r'⁻¹ * r)’ by METIS_TAC[mul_comm] \\
     POP_ORW \\
    ‘r⁻¹ * (1 − r'⁻¹ * r) = ((r⁻¹) * 1) - (r⁻¹ * (r'⁻¹ * r))’ by rw [sub_ldistrib] \\
     POP_ORW \\
    ‘r⁻¹ * (r'⁻¹ * r) = r⁻¹ * r * r'⁻¹’ by METIS_TAC[mul_assoc] \\
     POP_ORW \\
    ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv] \\
    ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     FULL_SIMP_TAC std_ss [] \\
     POP_ORW \\
    ‘r⁻¹ * 1 − 1 * r'⁻¹ = r⁻¹ − r'⁻¹’ by rw[mul_rone] \\
     POP_ORW \\
     rw[])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss[]
QED

Theorem liapounov_ineq_rv:
    !p u r r'. prob_space p /\ u IN lp_space r p ∧  u IN lp_space r' p ∧
               0 < r ∧
               r < r' ∧
               r' < PosInf  ==>
               seminorm r p u ≤ seminorm r' p u
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [prob_space_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘u’, ‘r’, ‘r'’]
            liapounov_ineq)
 >> impl_tac
 >> simp []
 >> DISCH_TAC
 >> Know ‘0 < r⁻¹ − r'⁻¹’
 >- (‘0 < r'’ by METIS_TAC [lt_trans] \\
     ‘inv(r') < inv(r)’ by METIS_TAC [inv_lt_antimono] \\
     METIS_TAC[sub_zero_lt])
 >> DISCH_TAC
 >> Know ‘1 powr (r⁻¹ − r'⁻¹) = 1’
 >- (MATCH_MP_TAC one_powr \\
     MATCH_MP_TAC lt_imp_le \\
     rw[])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ‘seminorm r' p u * 1 = seminorm r' p u’ by rw[mul_rone]
 >> FULL_SIMP_TAC std_ss []
QED

(* ------------------------------------------------------------------------- *)
(*  Converge_in_dist                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem converge_in_dist_cong_full:
    !p X Y A B m. prob_space p ∧
                 (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                 (!x. x IN p_space p ==> A x = B x) ==>
                 ((X --> A) (in_distribution p) <=> (Y --> B) (in_distribution p))
Proof
    rw [converge_in_dist_def, EXTREAL_LIM_SEQUENTIALLY]
 >> EQ_TAC >> rw []
    (* ∃N. ∀n.
          N ≤ n ⇒
          dist extreal_mr1
            (expectation p (Normal ∘ f ∘ real ∘ Y n),
             expectation p (Normal ∘ f ∘ real ∘ B)) < e *)
 >- (Q.PAT_X_ASSUM ‘ ∀f. bounded (IMAGE f 𝕌(:real)) ∧ f continuous_on 𝕌(:real)
                        ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ Y n) =
        expectation p (Normal ∘ f ∘ real ∘ X n)’
 >- (MATCH_MP_TAC expectation_cong \\ rw[])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
          expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw[])
 >> METIS_TAC [])
 >> Q.PAT_X_ASSUM ‘ ∀f. bounded (IMAGE f 𝕌(:real)) ∧ f continuous_on 𝕌(:real)
                        ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ Y n) =
        expectation p (Normal ∘ f ∘ real ∘ X n)’
 >- (MATCH_MP_TAC expectation_cong \\ rw[])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
        expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw[])
 >> METIS_TAC []
QED

Theorem converge_in_dist_cong:
    ∀p X Y Z m. prob_space p ∧
               (∀n x. m ≤ n ∧ x ∈ p_space p ⇒ X n x = Y n x) ⇒
               ((X ⟶ Z) (in_distribution p) ⇔ (Y ⟶ Z) (in_distribution p))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC converge_in_dist_cong_full
 >> Q.EXISTS_TAC ‘m’ >> rw []
QED


(* ------------------------------------------------------------------------- *)
(*  Normal density                                                           *)
(* ------------------------------------------------------------------------- *)

Overload ext_normal_density = “\mu sig. Normal o normal_density mu sig o real”

Definition normal_measure_def :
    normal_measure mu sig s =
    pos_fn_integral ext_lborel (\x. ext_normal_density mu sig x * indicator_fn s x)
End

Definition normal_rv_def :
     normal_rv X p mu sig <=> real_random_variable X p /\
                             !s. s IN subsets Borel ==>
                                 distribution p X s = normal_measure mu sig s
End

Definition third_moment_def:
    third_moment p X = central_moment p X 3
End

Definition absolute_third_moment_def:
    absolute_third_moment p X  = absolute_moment p X 0 3
End

Definition second_moments_def:
  second_moments p X n = SIGMA (λi. central_moment p (X i) 2) (count1 n)
End

Definition third_moments_def:
  third_moments p X n = SIGMA (λi. third_moment p (X i)) (count1 n)
End


(* ------------------------------------------------------------------------- *)

Theorem TAYLOR_REMAINDER:
  ∀(diff:num -> real -> real) n (x:real). ∃M t.
                                                abs (diff n t) ≤ M ⇒
                     abs (diff n t / (&FACT n:real) * x pow n) ≤ M / &FACT n * abs (x) pow n
Proof
    rpt GEN_TAC
    >> qexistsl [‘M’, ‘t’]
    >> STRIP_TAC
    >> ‘diff n t / &FACT n = diff n t * (&FACT n)⁻¹’ by METIS_TAC[real_div]
    >> POP_ORW
    >> ‘M / &FACT n =  M * (&FACT n)⁻¹’ by METIS_TAC[real_div]
    >> POP_ORW
    >> ‘!n. &0 < (&FACT n:real)’ by rw [REAL_LT, FACT_LESS]
    >> POP_ASSUM (MP_TAC o Q.SPEC ‘n’)
    >> DISCH_TAC
    >> ‘0 <= (&FACT n: real)’ by METIS_TAC [REAL_LT_IMP_LE]
    >> ‘&0 < (inv(&FACT n):real)’ by  METIS_TAC [REAL_INV_POS]
    >> ‘abs (diff n t) * inv(&FACT n) ≤ M  * inv(&FACT n)’ by
        METIS_TAC [REAL_LE_RMUL]
    >> ‘abs (inv(&FACT n:real)) = inv(&FACT n)’ by rw[ABS_REFL]
    >> ‘abs (diff n t) * abs (&FACT n)⁻¹ = abs (diff n t) * (&FACT n)⁻¹’ by rw[]
    >> ‘abs (diff n t) * abs (&FACT n)⁻¹ = abs (diff n t * (&FACT n)⁻¹)’ by METIS_TAC[ABS_MUL]
    >> ‘abs (diff n t * (&FACT n)⁻¹) ≤ M  * inv(&FACT n)’ by METIS_TAC[]
    >> ‘0 ≤ abs (x pow n)’ by METIS_TAC [REAL_ABS_POS]
    >> Cases_on ‘x pow n = 0’
    >- (‘x = 0’ by METIS_TAC [POW_ZERO] \\
        ‘abs x pow n = abs (x pow n)’ by rw[POW_ABS] \\
        ‘abs (x pow n) = 0’ by METIS_TAC[REAL_ABS_0] \\
        ‘diff n t * (&FACT n)⁻¹ * x pow n = 0’ by METIS_TAC [REAL_MUL_RZERO] \\
        ‘M * (&FACT n)⁻¹ * abs x pow n = 0’ by METIS_TAC [REAL_MUL_RZERO] \\
        METIS_TAC [])
    >> ‘0 < abs (x pow n)’ by METIS_TAC [ABS_NZ]
    >> ‘abs (diff n t * (&FACT n)⁻¹) * abs (x pow n) ≤ M * (&FACT n)⁻¹ * abs (x pow n)’ by
        METIS_TAC [REAL_LE_RMUL]
    >> ‘abs (diff n t * (&FACT n)⁻¹) * abs (x pow n) = abs (diff n t * (&FACT n)⁻¹ * x pow n)’ by
        METIS_TAC [GSYM ABS_MUL]
    >> FULL_SIMP_TAC std_ss []
    >> ‘abs (x pow n) = (abs x) pow n’ by METIS_TAC [POW_ABS]
    >> FULL_SIMP_TAC std_ss []
QED

Theorem TAYLOR_THEOREM:
    ∀f diff a x n.
                   a < x ∧ 0 < n ∧ diff 0 = f ∧
                  (∀m t. m < n ∧ a ≤ t ∧ t ≤ x ⇒ (diff m diffl diff (SUC m) t) t) ⇒
                     ∃t. a < t ∧ t < x ∧
                         f x =
                               sum (0,n) (λm. diff m a / &FACT m * (x − a) pow m) +
                               diff n t / &FACT n * (x − a) pow n
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = λx. f (x + a)’
 >> ‘∀x. g x = f (x + a)’ by rw[Abbr ‘g’]
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘x - a’)
 >> ‘f (x - a + a) = f x’ by METIS_TAC[REAL_SUB_ADD]
 >> POP_ORW
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘diff' = \n x. diff n (x + a)’
 >> MP_TAC (Q.SPECL [‘g’, ‘diff'’, ‘x - a’, ‘n’] MCLAURIN)
 >> impl_tac
 >- (CONJ_TAC
    (* 0 < x − a *)
     >- (rw[REAL_SUB_LT])
     >> CONJ_TAC
    (* 0 < n *)
     >> fs[]
     >> CONJ_TAC
    (* diff' 0 = g *)
     >- (rw[Abbr ‘diff'’])
     (* ∀m t. m < n ∧ 0 ≤ t ∧ t ≤ x − a ⇒ (diff' m diffl diff' (SUC m) t) t *)
     >> Q.UNABBREV_TAC ‘diff'’
     >> BETA_TAC
     >> qx_genl_tac [‘m’, ‘t’]
     >> STRIP_TAC
     >> ‘a ≤ t + a’ by rw[REAL_LE_ADDL]
     >> ‘t + a ≤ x’ by METIS_TAC[REAL_LE_SUB_LADD]
     >> Q.PAT_X_ASSUM ‘∀m t. m < n ∧ a ≤ t ∧ t ≤ x ⇒
                             (diff m diffl diff (SUC m) t) t’
       (MP_TAC o Q.SPECL [‘m’, ‘t + a’])
     >> DISCH_TAC
     >> MP_TAC (Q.SPECL [‘diff (m:num)’, ‘λx. (x + a)’, ‘diff (SUC m) (t + a:real)’, ‘1’, ‘t’] DIFF_CHAIN)
     >> impl_tac
     >- (CONJ_TAC
         >- (BETA_TAC \\
             METIS_TAC [])
         (* ((λx. x + a) diffl 1) t *)
         >> Know ‘((λx. x + a) diffl (1 + 0)) t’
         >- (MP_TAC (Q.SPECL [‘λx. x’, ‘λx. a’, ‘1’, ‘0’, ‘t’] DIFF_ADD) \\
             impl_tac \\
             METIS_TAC [DIFF_X, DIFF_CONST] \\
             BETA_TAC \\
             simp[])
         >> simp[REAL_ADD_RID])
         >> simp[])
 >> simp[]
 >> DISCH_THEN (Q.X_CHOOSE_TAC ‘t’)
 >> Q.EXISTS_TAC ‘t + a’
 >> CONJ_TAC
 >- (rw[REAL_LT_ADDL])
 >> CONJ_TAC
 >- (rw[REAL_LT_ADD_SUB])
 >> Know ‘∀m. diff' m 0 = diff m a’
    >- (Q.UNABBREV_TAC ‘diff'’ \\
        BETA_TAC \\
        simp[])
 >> DISCH_TAC
 >> simp[]
QED


Theorem TAYLOR_CLT_LEMMA:
  ∀diff (f:real -> real) x y M.
                              0 < y ∧ diff (0:num) = f ∧
                              (∀m t.  m < 3 ∧ x ≤ t ∧ t ≤ x + y ⇒ (diff m diffl diff (SUC m) t) t) ∧
                              M = sup {diff 3 x | x | T} ⇒
                              abs (f (x + y) - (f x + diff 1 x * y + diff 2 x / 2 * y pow 2)) ≤
                              M / 6 * abs y pow 3
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘diff’, ‘x’, ‘x + y’, ‘3’] TAYLOR_THEOREM)
 >> simp[]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘t’ STRIP_ASSUME_TAC)
 >> ‘x + y − x = y’ by rw[REAL_ADD_SUB]
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘sum (0,3) (λm. diff m x / &FACT m * y pow m) =
           (f x + diff 1 x * y + diff 2 x / 2 * y²)’
 >- (EVAL_TAC \\
     simp[])
 >> fs[]
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘Z = f x + diff 1 x * y + diff 2 x / 2 * y²’
 >> fs[]
 >> ‘Z + y³ * (&FACT 3)⁻¹ * diff 3 t − Z =   y³ * (&FACT 3)⁻¹ * diff 3 t’ by rw[REAL_ADD_SUB]
 >> POP_ORW
 >> Q.UNABBREV_TAC ‘Z’
 >> ‘inv(&FACT 3) = (inv(6):real)’ by EVAL_TAC
 >> POP_ORW
 >> simp[]
 >> ‘abs (1 / 6 * (y³ * diff 3 t)) = abs (1/6) * abs (y³ * diff 3 t)’ by rw[ABS_MUL]
 >> POP_ORW
 >> ‘6 * (abs (1 / 6) * abs (y³ * diff 3 t)) = abs (y³ * diff 3 t)’
     by rw[GSYM REAL_MUL_ASSOC, ABS_REFL, REAL_MUL_RINV, REAL_MUL_RID]
 >> POP_ORW
 >> ‘abs (y³ * diff 3 t) = abs (y³) * abs (diff 3 t)’ by rw[ABS_MUL]
 >> POP_ORW
 >> ‘abs (y pow 3) = abs y pow 3’ by METIS_TAC[POW_ABS]
 >> POP_ORW
 >> MATCH_MP_TAC REAL_LE_LMUL1
 >> CONJ_TAC
 >- (METIS_TAC[ABS_POS, POW_POS])
 >> cheat
QED


Theorem normal_absolute_third_moment:
    ∀p X sig. normal_rv X p 0 sig ⇒
              absolute_third_moment p X = sqrt (8 / π)  *  variance p X  * sqrt (variance p X)
Proof
    cheat
QED

Definition BigO_def:
  BigO f g ⇔ ∃(M:real) x0. ∀x. x0 ≤ (x:real) ⇒
                                abs (f x) ≤ M * abs (g x)
End

Theorem IN_MEASURABLE_BOREL_SUM_CMUL:
    ∀a f g s z.
               FINITE s ∧ sigma_algebra a ∧ (∀i. i ∈ s ⇒ f i ∈ Borel_measurable a) ∧
               (∀x. x ∈ space a ⇒ g x = Normal z * ∑ (λi. f i x) s) ⇒
               g ∈ Borel_measurable a
Proof
  RW_TAC std_ss []
  >> Cases_on `Normal z = 0`
  >- METIS_TAC [IN_MEASURABLE_BOREL_CONST, mul_lzero]
  >> Q.ABBREV_TAC ‘h = λx. ∑ (λi. (f: β -> α -> extreal) i x) s’
  >> ‘∀x. h x = ∑ (λi. f i x) s’ by rw[Abbr ‘h’]
  >> MP_TAC (Q.SPECL [‘a’, ‘(f: 'b -> 'a -> extreal)’, ‘h’, ‘s’]
                      IN_MEASURABLE_BOREL_SUM')
  >> impl_tac
  >- (METIS_TAC[])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘a’, ‘h’, ‘λx. Normal z * h x’, ‘z’]
              IN_MEASURABLE_BOREL_CMUL)
  >> impl_tac
  >- (METIS_TAC[])
  >> ‘!x. x IN space a ==> (Normal z * h x = g x)’ by rw [Abbr ‘h’]
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘a’, ‘g’, ‘λx. Normal z * h x’]
              IN_MEASURABLE_BOREL_EQ')
  >> impl_tac
  >> BETA_TAC
  >- (METIS_TAC[])
  >> simp[]
QED

Theorem real_random_variable_sum_cmul:
  ∀p X J r.
    prob_space p ∧ FINITE J ∧ (∀i. i ∈ J ⇒ real_random_variable (X i) p) ⇒
    real_random_variable (λx. Normal r * ∑ (λn. X n x) J) p
Proof
  rw [real_random_variable_cmul, real_random_variable_sum]
QED

Theorem central_limit:
  ∀p X Y N s b. prob_space p ∧
                normal_rv N p 0 1 ∧
               (∀i. real_random_variable (X i) p) ∧
               (∀i j. indep_vars p (X i) (X j) Borel Borel) ∧
               (∀i. normal_rv (Y i) p 0 (real (standard_deviation p (X 0)))) ∧
               (∀(i:num). real_random_variable (Y i) p) ∧
               (∀i j. indep_vars p (Y i) (Y j) Borel Borel) ∧
               (∀i j. indep_vars p (X i) (Y j) Borel Borel) ∧
               (∀i. expectation p (X i) = 0) ∧
               (∀i. central_moment p (X i) 2 < PosInf) ∧
               (∀i. third_moment p (X i) < PosInf) ∧
               (∀n. s n = sqrt (second_moments p X n)) ∧
               (∀n. b n = third_moments p X n) ∧
               ((\n. b n / (s n pow 3)) --> 0) sequentially ⇒
               ((\n x. (SIGMA (λi. X i x) (count1 n)) / s n) --> N) (in_distribution p)
Proof
     rpt STRIP_TAC
  >> Q.ABBREV_TAC ‘Z = λn x. ∑ (λi. X i x) (count1 n) / s n’
  >> fs[normal_rv_def]
  >> Know ‘∀i. real_random_variable (Z i) p’
     >- (rw[Abbr ‘Z’]
     >> Q.ABBREV_TAC ‘C = sqrt (second_moments p X i)’
     >> Cases_on ‘C = 0’
     >- (rw[Abbr ‘C’] \\
         cheat)
     >> Know ‘0 ≤ C’
        >- (Q.UNABBREV_TAC ‘C’ \\
            MATCH_MP_TAC sqrt_pos_le \\
            rw[second_moments_def] \\
            (* 0 < ∑ (λi. central_moment p (X i) 2) (count1 i) *)
            Q.ABBREV_TAC ‘G = λi. central_moment p (X i) 2’ \\
            MATCH_MP_TAC (INST_TYPE [alpha |-> “:num”] EXTREAL_SUM_IMAGE_POS) \\
            simp[] \\
            (* ∀x. x < SUC i ⇒ 0 < G x *)
            rw[Abbr ‘G’, central_moment_def]\\
            ‘moment p (X x) 0 2 = second_moment p (X x) 0’ by EVAL_TAC \\
            simp[] \\
            MP_TAC (Q.SPECL [‘p’, ‘X (x:num)’, ‘0’]
                    second_moment_pos) \\
            simp[] \\
            DISCH_TAC)
      >> DISCH_TAC
      >> ‘0 < C’ by rw[lt_le]
      >> ‘inv(C) ≠ NegInf ∧ inv(C) ≠ PosInf’ by METIS_TAC[inv_not_infty]
      >> ‘∃r. Normal r = inv(C)’ by METIS_TAC[extreal_cases]
      >> Q.ABBREV_TAC ‘D = λx. ∑ (λi. X i x) (count1 i)’
      >> ‘∀x. D x = ∑ (λi. X i x) (count1 i)’ by rw[Abbr ‘D’]
      >> Know ‘∀x. D x ≠ NegInf’
         >- (rw[Abbr ‘D’] \\
             MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
             cheat)
      >> DISCH_TAC
      >> Know ‘∀x. D x ≠ PosInf’
         >- (rw[Abbr ‘D’] \\
             MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
             cheat)
      >> DISCH_TAC
      >> ‘∀x. D x / C = Normal r * D x’ by METIS_TAC[div_eq_mul_linv]
      >> rw[Abbr ‘D’]
      >> FULL_SIMP_TAC std_ss [] (* unexpected return *)
      >> ‘∀x. real_random_variable (λx. Normal r * ∑ (λi. X i x) (count1 i)) p’ by
              rw[real_random_variable_sum_cmul]
      >> cheat)
  >> DISCH_TAC
  >> rw [converge_in_dist_alt']
  >> cheat
QED


(* ------------------------------------------------------------------------- *)
(*  Moment generating function                                               *)
(* ------------------------------------------------------------------------- *)

Definition mgf_def:
   mgf p X s =  expectation p (\x. exp (Normal s * X x))
End

Theorem mgf_0:
    !p X. prob_space p ==> mgf p X 0 = 1
Proof
    RW_TAC std_ss [mgf_def, mul_lzero, exp_0, normal_0]
 >> MATCH_MP_TAC expectation_const >> art[]
QED

Theorem real_random_variable_exp:
    ∀p X r. prob_space p ∧ real_random_variable X p ⇒ real_random_variable (λx. exp (X x)) p
Proof
    rpt GEN_TAC
 >> simp [real_random_variable, prob_space_def, p_space_def, events_def]
 >> STRIP_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP >>  qexists_tac ‘X’ >> rw [])
 >> Q.X_GEN_TAC ‘x’
 >> DISCH_TAC
 >> ‘?z. X x = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw[extreal_exp_def]
QED

Theorem real_random_variable_exp_normal:
    ∀p X r. prob_space p ∧ real_random_variable X p ⇒
            real_random_variable (λx. exp (Normal s * X x)) p
Proof
    rw [real_random_variable_cmul, real_random_variable_exp]
QED

Theorem mgf_linear:
    ∀p X a b s. prob_space p ∧ real_random_variable X p ∧
                integrable p (λx. exp (Normal (a * s) * X x))  ⇒
                mgf p (λx.( Normal a * X x) + Normal b) s =  (exp (Normal s * Normal b)) * mgf p X (a * s)
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘ expectation p (λx. exp (Normal s * ((Normal a * X x) + Normal b)))
         = expectation p (λx. exp ((Normal s * (Normal a * X x)) + Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> AP_TERM_TAC
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases] >> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[add_ldistrib_normal2]) >> Rewr'
 >> Know ‘expectation p
         (λx. exp (Normal s * (Normal a * X x) + Normal s * Normal b)) =
          expectation p (λx. (exp (Normal s * (Normal a * X x))) * exp (Normal s * Normal b))’
 >- (MATCH_MP_TAC expectation_cong
     >> rw[exp_add]
     >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases]>> rw[]
     >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃e. Normal s * Normal d = Normal e’ by METIS_TAC [extreal_mul_eq] >> rw[]
     >> ‘∃f. Normal s * Normal b = Normal f’ by METIS_TAC [extreal_mul_eq] >> rw[exp_add]) >> Rewr'
 >> ‘∃g. exp (Normal s * Normal b) = Normal g’ by  METIS_TAC [extreal_mul_eq, normal_exp]
 >> rw[]
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
 >> rw [mul_assoc, extreal_mul_eq]
 >> HO_MATCH_MP_TAC expectation_cmul
 >> ASM_REWRITE_TAC []
QED

Theorem mgf_sum:
    !p X Y s . prob_space p ∧ real_random_variable X p  ∧
               real_random_variable Y p  ∧
               indep_vars p X Y Borel Borel ∧
               mgf p (\x. X x + Y x) s ≠ PosInf ∧
               mgf p X s ≠ PosInf ∧
               mgf p Y s ≠ PosInf  ==>
               mgf p (\x. X x + Y x) s = mgf p X s * mgf p Y s
Proof
    rw [mgf_def, real_random_variable_def]
 >> Know ‘expectation p (\x. exp (Normal s * (X x + Y x))) =
          expectation p (\x. exp ((Normal s * X x) + (Normal s * Y x)))’
 >-(MATCH_MP_TAC expectation_cong >> rw[] >> AP_TERM_TAC
    >> MATCH_MP_TAC add_ldistrib_normal >> rw[])
    >> Rewr'
 >> Know ‘expectation p (λx. exp (Normal s * X x + Normal s * Y x)) =
          expectation p (λx. exp (Normal s * X x) * exp (Normal s * Y x))’
 >- (MATCH_MP_TAC expectation_cong  >> rw[] >> MATCH_MP_TAC exp_add >> DISJ2_TAC
     >> ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases]
     >> ‘∃b. Y x = Normal b’ by METIS_TAC [extreal_cases]
     >> rw[extreal_mul_eq]) >> Rewr'
 >> HO_MATCH_MP_TAC indep_vars_expectation
 >> simp[]
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* real_random_variable (λx. exp (Normal s * X x)) p *)
 >- (MATCH_MP_TAC real_random_variable_exp_normal
     >> fs[real_random_variable, random_variable_def])
 >> CONJ_TAC
   (* indep_vars p (λx. exp (Normal s * X x)) (λx. exp (Normal s * Y x)) Borel Borel *)
 >- (Q.ABBREV_TAC ‘f = λx. exp (Normal s * x)’
     >> simp[]
     >> MATCH_MP_TAC (REWRITE_RULE [o_DEF] indep_rv_cong) >> csimp[]
     >> Q.UNABBREV_TAC ‘f’
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> simp[] >> Q.EXISTS_TAC ‘λx. Normal s * x’ >> simp[SIGMA_ALGEBRA_BOREL]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘λx. x’, ‘s’]
     >> simp[SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I])
 >> Know ‘(λx. exp (Normal s * X x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * X x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘X’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Know ‘(λx. exp (Normal s * Y x)) ∈ Borel_measurable (measurable_space p)’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
     >> Q.EXISTS_TAC ‘λx. Normal s * Y x’
     >> fs [prob_space_def, measure_space_def]
     >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
     >> qexistsl [‘Y’, ‘s’] >> simp[random_variable_def]
     >> fs [random_variable_def, p_space_def, events_def])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘f = λx. exp (Normal s * X x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  f x’ by METIS_TAC [exp_pos]
 >> Q.ABBREV_TAC ‘g = λx. exp (Normal s * Y x)’ >> simp[]
 >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  g x’ by METIS_TAC [exp_pos]
 >> CONJ_TAC (* integrable p f *)
    >- (Suff ‘ pos_fn_integral p f <> PosInf’
        >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
        >> ‘∫ p f = ∫⁺ p f ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
        >> METIS_TAC [expectation_def]
        >> simp[])
    >- (Suff ‘ pos_fn_integral p g <> PosInf’
        >- FULL_SIMP_TAC std_ss [prob_space_def, p_space_def, integrable_pos, expectation_def]
        >> ‘∫ p g = ∫⁺ p g ’ by METIS_TAC[integral_pos_fn, prob_space_def, p_space_def]
        >> METIS_TAC [expectation_def])
QED

(*independent_identical_distribution*)
Definition iid_def:
    iid p X E A J ⇔ identical_distribution p X E J ∧
                     pairwise_indep_vars p X A J
End

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory "central_limit";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [4] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
  [5] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Edition).
      World Scientific Publishing Company (2006).


 *)
