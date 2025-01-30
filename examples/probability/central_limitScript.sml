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

open distributionTheory realaxTheory;

val _ = new_theory "central_limit";

Theorem liapounov_ineq_lemma:
    !m u p. measure_space m ∧
            measure m (m_space m) < PosInf ∧
            1 < p ∧ p < PosInf ∧
            u ∈ lp_space p m  ⇒
            ∫⁺ m (λx. abs (u x)) ≤ seminorm p m u * ((measure m (m_space m)) powr (1 - inv(p)))
Proof
    rpt STRIP_TAC
 >> ‘p ≠ PosInf’ by rw [lt_imp_ne]
 >> ‘0 < p’ by METIS_TAC [lt_trans, lt_01]
 >> ‘p ≠ 0’ by rw [lt_imp_ne]
 >> ‘inv(p) ≠ NegInf ∧ inv(p) ≠ PosInf’ by rw [inv_not_infty]
 >> ‘p ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘0 < inv (p)’ by METIS_TAC [inv_pos']
 >> ‘inv(p) ≠ 0’ by rw [lt_imp_ne]
 >> Know ‘inv (p) < 1’
 >- (‘1 * inv(p) < p * inv(p)’ by rw [lt_rmul] \\
     ‘p / p = p * inv(p)’ by rw [div_eq_mul_rinv] \\
     ‘p / p = 1’ by METIS_TAC [div_refl_pos] \\
     ‘inv(p) = 1 * inv(p)’ by rw [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘0 < 1 - inv(p)’ by rw [sub_zero_lt]
 >> ‘1 - inv(p) ≠ 0’ by rw [lt_imp_ne]
 >> Know ‘1 - inv(p) ≠ NegInf’
 >- (‘∃a. inv(p) = Normal a’ by METIS_TAC [extreal_cases] \\
     ‘∃c. Normal 1 - Normal a = Normal c’ by METIS_TAC [extreal_sub_def] \\
     Know ‘1 - inv(p) = Normal c’
     >- (‘1 = Normal 1’ by rw[] >> rw[]) >> rw [])
 >> DISCH_TAC
 >> Know ‘1 - inv(p) ≠ PosInf’
 >- (‘∃b. inv(p) = Normal b’ by METIS_TAC [extreal_cases]
     >> ‘∃d. Normal 1 - Normal b = Normal d’ by METIS_TAC [extreal_sub_def]
     >> Know ‘1 - inv(p) = Normal d’
     >- (‘1 = Normal 1’ by rw [] >> rw []) >> rw [])
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
         MP_TAC (Q.SPECL [‘p’, ‘1’] inv_lt_antimono) \\
         simp [lt_01, inv_one]) \\
      (*  1 − p⁻¹ ≠ +∞ *)
    rw [])
 >> DISCH_TAC
 >> Know ‘q ≠ PosInf’
 >- (Q.UNABBREV_TAC ‘q’ \\
     rw [inv_not_infty])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘u’, ‘λx. 1’, ‘p’, ‘q’]
            Hoelder_inequality')
 >> impl_tac
 >> simp[]
 (* (λx. 1) ∈ lp_space q m*)
 >- (rw [lp_space_def]
 (*  (λx. 1) ∈ Borel_measurable (measurable_space m) *)
     >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' \\
         rw [measure_space_def])
    (* ∫⁺ m (λx. abs 1 powr q) ≠ +∞ *)
     >> ‘abs 1 = 1’ by rw [abs_refl]
     >> rw []
     >> Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw [])
     >> DISCH_TAC
     >> simp []
    (* ∫⁺ m (λx. 1) ≠ +∞ *)
     >> MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const)
     >> impl_tac
     >> simp []
     >> DISCH_TAC
     >> ‘1 = Normal 1’ by rw []
    (*  measure m (m_space m) <> +∞ *)
     >> rw []
     >> ‘measure m (m_space m) ≠ +∞’ by rw [lt_imp_ne]
     >> rw [mul_not_infty])
 >> DISCH_TAC
 >> Know ‘seminorm q m (λx. 1) = ((measure m (m_space m)) powr (1 - inv(p)))’
 >- (rw [seminorm_def] \\
     Know ‘inv (q) = 1 - inv (p)’
     >- (Q.UNABBREV_TAC ‘q’ \\
         rw [inv_inv]) \\
     DISCH_TAC \\
     rw [] \\
    ‘abs 1 = 1’ by rw [abs_refl] \\
     rw [] \\
     Know ‘1 powr q = 1’
     >- (MATCH_MP_TAC one_powr \\
         MATCH_MP_TAC lt_imp_le \\
         rw []) \\
     DISCH_TAC  \\
    ‘1 = Normal 1’ by rw [] \\
     simp [] \\
     Know ‘∫⁺ m (λx. Normal 1) =  measure m (m_space m)’
     >- (MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const) \\
         impl_tac \\
         simp [] \\
        ‘1 * measure m (m_space m) =  measure m (m_space m) ’ by rw [mul_lone] \\
         simp [] \\
         DISCH_TAC \\
         METIS_TAC []) \\
     DISCH_TAC \\
     simp [])
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
 >> ‘r ≠ PosInf ∧ r' ≠ PosInf ’ by rw [lt_imp_ne]
 >> ‘NegInf < r ∧ NegInf < r'’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> ‘r ≠ NegInf ∧ r' ≠ NegInf’ by METIS_TAC [lt_imp_ne]
 >> Know ‘inv r <> PosInf /\ inv r <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> Know ‘inv r' <> PosInf /\ inv r' <> NegInf’
 >- (MATCH_MP_TAC inv_not_infty >> art []) >> DISCH_TAC
 >> ‘0 < inv (r) ∧ 0 < inv (r')’ by METIS_TAC [inv_pos']
 >> ‘inv(r) ≠ 0 ∧ inv(r') ≠ 0’ by rw [lt_imp_ne]
 >> ‘inv(r') * r ≠ NegInf ∧ inv(r') * r ≠ PosInf’ by METIS_TAC [mul_not_infty2]
 >>  ‘r' * inv(r) ≠ NegInf ∧ r' * inv(r) ≠ PosInf’ by METIS_TAC [mul_not_infty2]
 >> Know ‘1 < r' * r⁻¹’
 >- (‘r * inv(r) < r' * inv(r)’ by rw [lt_rmul] \\
     ‘r / r = r * inv(r)’ by rw [div_eq_mul_rinv] \\
     ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘0 < r' * inv(r)’ by METIS_TAC [lt_01, lt_trans]
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
             rw []) \\
        (* r ≠ +∞ *)
             simp [])
      (* ∫⁺ m (λx. abs (abs (u x) powr r) powr (r' * r⁻¹)) ≠ +∞ *)
      >> ‘∀x. abs (abs (u x) powr r) = abs (u x) powr r’ by rw [abs_pos, powr_pos, abs_refl]
      >> POP_ORW
      >> ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) = abs (u x) powr (r * (r' * r⁻¹))’ by rw [powr_powr]
      >> POP_ORW
      >> ‘r * (r' * r⁻¹) = r * inv(r) * r'’ by PROVE_TAC [mul_comm, mul_assoc]
      >> ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv]
      >> ‘r * inv(r) = inv(r) * r’ by PROVE_TAC [mul_comm]
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
 >- (rw [seminorm_def] \\
     ‘∀x. (abs (u x) powr r) powr (r' * r⁻¹) =  abs (u x) powr (r * (r' * r⁻¹))’ by rw [abs_pos, powr_powr] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r * (r' * r⁻¹)) = abs (u x) powr (r⁻¹ * r * r')’ by PROVE_TAC [mul_assoc, mul_comm] \\
     POP_ORW \\
     ‘∀x. abs (u x) powr (r⁻¹ * r * r') = abs (u x) powr r'’ by rw [mul_linv_pos, mul_lone] \\
     POP_ORW \\
     ‘inv(r' * inv(r)) = inv(r') * r’ by rw [inv_mul, inv_inv] \\
     POP_ORW \\
     Know ‘0 ≤ ∫⁺ m (λx. abs (u x) powr r')’
     >- (MATCH_MP_TAC pos_fn_integral_pos \\
         simp[] \\
        (* ∀x. x ∈ m_space m ⇒ 0 ≤ abs (u x) powr r'*)
         METIS_TAC [abs_pos, powr_pos]) \\
     DISCH_TAC \\
     ‘∫⁺ m (λx. abs (u x) powr r') powr (r'⁻¹ * r) = (∫⁺ m (λx. abs (u x) powr r') powr r'⁻¹) powr r’
         by rw [GSYM powr_powr])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘A =  ∫⁺ m (λx. abs (u x) powr r)’
 >> Q.ABBREV_TAC ‘B =  seminorm r' m u powr r * mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp []
 >> Know ‘A powr inv(r) ≤ B powr inv(r)’
 >- (Know ‘0 ≤ A’
     >- (rw [Abbr ‘A’] \\
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
 >> ‘∫⁺ m (λx. abs (u x) powr r) powr inv(r) = seminorm r m u’ by rw [seminorm_def]
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘C = seminorm r' m u’
 >> Q.ABBREV_TAC ‘D = mu powr (1 − (r' * r⁻¹)⁻¹)’
 >> simp[]
 >> Know ‘(C powr r * D) powr r⁻¹ = C * D powr inv(r)’
 >- (‘0 ≤ C’ by PROVE_TAC [seminorm_pos] \\
     ‘0 ≤ C powr r’ by PROVE_TAC [powr_pos] \\
     ‘0 ≤ D’ by METIS_TAC [powr_pos] \\
     ‘(C powr r * D) powr r⁻¹ = (C powr r) powr r⁻¹ * D powr inv(r)’ by METIS_TAC [mul_powr] \\
     ‘(C powr r) powr r⁻¹ = C powr (r * inv(r))’ by METIS_TAC [powr_powr] \\
     ‘C powr (r * inv(r)) = C’ by METIS_TAC [GSYM div_eq_mul_rinv, div_refl_pos, powr_1] \\
      simp [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> Q.UNABBREV_TAC ‘C’
 >> Q.UNABBREV_TAC ‘D’
 >> Know ‘(mu powr (1 − (r' * r⁻¹)⁻¹)) powr r⁻¹ =
           mu powr (r⁻¹ − r'⁻¹)’
 >- (Know ‘r * inv(r') < 1’
     >- (‘r * inv(r') < r' * inv(r')’ by rw [lt_rmul] \\
         ‘r' / r' = r' * inv(r')’ by rw [div_eq_mul_rinv] \\
         ‘r' / r' = 1’ by METIS_TAC [div_refl_pos] \\
          METIS_TAC []) \\
     DISCH_TAC \\
    ‘r * r'⁻¹ = r'⁻¹ * r’ by METIS_TAC [mul_comm] \\
     FULL_SIMP_TAC std_ss [] \\
    ‘(r' * r⁻¹)⁻¹ = inv(r') * r’ by METIS_TAC [inv_mul, inv_inv, mul_comm] \\
     simp [] \\
    ‘0 < 1 - inv(r') * r’ by METIS_TAC [sub_zero_lt] \\
     Know ‘1 − r'⁻¹ * r ≠ PosInf’
     >- (‘∃b. r'⁻¹ * r  = Normal b’ by METIS_TAC [extreal_cases] \\
          rw [sub_not_infty]) \\
     DISCH_TAC \\
    ‘(mu powr (1 − r'⁻¹ * r)) powr r⁻¹ = mu powr ((1 − r'⁻¹ * r) * inv(r))’
         by METIS_TAC [powr_powr] \\
     POP_ORW \\
    ‘(1 − r'⁻¹ * r) * r⁻¹ =  r⁻¹ * (1 − r'⁻¹ * r)’ by METIS_TAC [mul_comm] \\
     POP_ORW \\
    ‘r⁻¹ * (1 − r'⁻¹ * r) = ((r⁻¹) * 1) - (r⁻¹ * (r'⁻¹ * r))’ by rw [sub_ldistrib] \\
     POP_ORW \\
    ‘r⁻¹ * (r'⁻¹ * r) = r⁻¹ * r * r'⁻¹’ by METIS_TAC [mul_assoc] \\
     POP_ORW \\
    ‘inv(r) * r = r / r’ by rw [GSYM div_eq_mul_linv] \\
    ‘r / r = 1’ by METIS_TAC [div_refl_pos] \\
     FULL_SIMP_TAC std_ss [] \\
     POP_ORW \\
    ‘r⁻¹ * 1 − 1 * r'⁻¹ = r⁻¹ − r'⁻¹’ by rw [mul_rone] \\
     POP_ORW \\
     rw [])
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
     METIS_TAC [sub_zero_lt])
 >> DISCH_TAC
 >> Know ‘1 powr (r⁻¹ − r'⁻¹) = 1’
 >- (MATCH_MP_TAC one_powr \\
     MATCH_MP_TAC lt_imp_le \\
     rw [])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ‘seminorm r' p u * 1 = seminorm r' p u’ by rw [mul_rone]
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
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
          expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> METIS_TAC [])
 >> Q.PAT_X_ASSUM ‘ ∀f. bounded (IMAGE f 𝕌(:real)) ∧ f continuous_on 𝕌(:real)
                        ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
 >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ Y n) =
        expectation p (Normal ∘ f ∘ real ∘ X n)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
 >> sg ‘expectation p (Normal ∘ f ∘ real ∘ B) =
        expectation p (Normal ∘ f ∘ real ∘ A)’
 >- (MATCH_MP_TAC expectation_cong \\ rw [])
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
(*  Big O Notation                                                           *)
(* ------------------------------------------------------------------------- *)

Definition BigO_def:
  BigO f g ⇔ ∃(c:real) (n0:num). 0 < c ∧
                                  ∀(n:num). n0 ≤ n ⇒
                                            abs (f n) ≤ c * abs (g n)
End

Theorem BigO_MUL:
  ∀f1 g1 f2 g2. BigO f1 g1 ∧
                BigO f2 g2 ⇒ BigO (λn. f1 n * f2 n) (λn. g1 n * g2 n)
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘c * c'’, ‘MAX n0 n0'’]
 >> rw [REAL_MAX_LE, REAL_LT_MUL']
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n) * abs (f2 n) ≤ c * abs (g1 n) * (c' * abs (g2 n))’
 >- (MATCH_MP_TAC REAL_LE_MUL2 \\
     fs [] \\
     rw [])
 >> DISCH_TAC
 >> ‘abs (f1 n) * abs (f2 n) = abs (f1 n * f2 n)’ by rw [GSYM ABS_MUL]
 >> ‘c * abs (g1 n) * (c' * abs (g2 n)) = c * c' * abs (g1 n * g2 n)’
     by rw [REAL_MUL_ASSOC, REAL_MUL_COMM, GSYM ABS_MUL]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem BigO_ADD:
  ∀f1 f2 g1 g2. BigO f1 g1 ∧ BigO f2 g2 ⇒
                BigO (λn. f1 n + f2 n) (λn. abs (g1 n) + abs (g2 n))
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘max c c'’, ‘MAX n0 n0'’]
 >> CONJ_TAC
 (* 0 < max c c' *)
 >- (rw [REAL_LT_MAX])
 >> GEN_TAC
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n + f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
 >- (‘abs (f1 n + f2 n) ≤ abs (f1 n) + abs (f2 n)’ by rw [ABS_TRIANGLE] \\
     Know ‘abs (f1 n) + abs (f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
     >- (MATCH_MP_TAC REAL_LE_ADD2 \\
         METIS_TAC []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ abs((abs (g1 n) + abs (g2 n))) * max c c'’
 >- (Know ‘c * abs (g1 n) ≤ max c c' * abs (g1 n)’
     >- (‘c ≤ max c c'’ by rw [REAL_LE_MAX1] \\
         Cases_on ‘abs (g1 n) = 0’
         >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
             ‘0 ≤ abs (g1 n)’ by METIS_TAC [ABS_POS]  \\
             ‘0 < abs (g1 n)’ by METIS_TAC [REAL_LT_LE] \\
         simp [GSYM REAL_LE_LMUL]) \\
    DISCH_TAC \\
    Know ‘c' * abs (g2 n) ≤ max c c' * abs (g2 n)’
    >- (‘c' ≤ max c c'’ by rw [REAL_LE_MAX2] \\
        Cases_on ‘abs (g2 n) = 0’
        >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
            ‘0 ≤ abs (g2 n)’ by METIS_TAC [ABS_POS]  \\
            ‘0 < abs (g2 n)’ by  METIS_TAC [REAL_LT_LE] \\
            simp [GSYM REAL_LE_LMUL]) \\
    DISCH_TAC \\
    Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ max c c' * abs (g1 n) + max c c' * abs (g2 n)’
    >- (MATCH_MP_TAC REAL_LE_ADD2 \\
        METIS_TAC []) \\
    DISCH_TAC \\
    ‘max c c' * abs (g1 n) + max c c' * abs (g2 n) = (abs (g1 n) + abs (g2 n)) * max c c'’
    by rw [GSYM REAL_ADD_RDISTRIB] \\
    FULL_SIMP_TAC std_ss [] \\
    Know ‘(abs (g1 n) + abs (g2 n)) * max c c' = abs((abs (g1 n) + abs (g2 n))) * max c c'’
    >- (Q.ABBREV_TAC ‘A =  abs (g1 n) + abs (g2 n)’ \\
        Know ‘0 ≤ A’
        >- (rw [abs] \\
            METIS_TAC [ABS_POS, REAL_LE_ADD]) \\
        DISCH_TAC \\
        ‘abs A = A’ by METIS_TAC [abs] \\
        simp []) \\
    DISCH_TAC \\
    METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem BigO_ADD_MAX:
  ∀f1 f2 g1 g2. BigO f1 g1 ∧ BigO f2 g2 ⇒
                BigO (λn. f1 n + f2 n) (λn. max (abs(g1 n)) (abs(g2 n)))
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘c + c'’, ‘MAX n0 n0'’]
 >> CONJ_TAC
 >- (METIS_TAC [REAL_LT_ADD])
 >> GEN_TAC
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [MAX_LE]
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f1 n) ≤ c * abs (g1 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Q.PAT_X_ASSUM ‘∀n. n0' ≤ n ⇒ abs (f2 n) ≤ c' * abs (g2 n)’
     (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> Know ‘abs (f1 n + f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
 >- (‘abs (f1 n + f2 n) ≤ abs (f1 n) + abs (f2 n)’ by rw [ABS_TRIANGLE] \\
     Know ‘abs (f1 n) + abs (f2 n) ≤ c * abs (g1 n) + c' * abs (g2 n)’
     >- (MATCH_MP_TAC REAL_LE_ADD2 \\
         METIS_TAC []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘A = max (abs (g1 n)) (abs (g2 n))’
 >> rw []
 >> Know ‘c * abs (g1 n) + c' * abs (g2 n) ≤ abs A * (c + c')’
 >- (‘abs (g1 n) ≤ A’ by METIS_TAC [Abbr ‘A’, REAL_LE_MAX1] \\
     ‘abs (g2 n) ≤ A’ by METIS_TAC [Abbr ‘A’, REAL_LE_MAX2] \\
     ‘c * abs (g1 n) ≤ c * A’ by simp [REAL_LE_LMUL] \\
     ‘c' * abs (g2 n) ≤ c' * A’ by simp [REAL_LE_LMUL] \\
     ‘0 ≤ abs (g1 n)’ by METIS_TAC [ABS_POS]\\
     ‘0 ≤ A’ by METIS_TAC [REAL_LE_TRANS] \\
     ‘A = abs A’ by rw [abs] \\
     ‘c * abs (g1 n) + c' * abs (g2 n) ≤  c * A + c' * A’ by METIS_TAC [REAL_LE_ADD2] \\
     ‘c * A + c' * A = A * (c + c')’ by rw [GSYM REAL_ADD_RDISTRIB] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> METIS_TAC [REAL_LE_TRANS]
QED

Theorem BigO_MUL_CONST:
    ∀f g k. k ≠ 0 ∧ BigO f g ⇒ BigO (λn. k * f n) g
Proof
    rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [BigO_def]
 >> qexistsl_tac [‘abs k * c’, ‘n0’]
 >> CONJ_TAC
 (* 0 < abs k * c *)
 >- (‘0 < abs k’ by rw [ABS_NZ'] \\
     METIS_TAC [REAL_LT_RMUL_0])
 >> GEN_TAC
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘∀n. n0 ≤ n ⇒ abs (f n) ≤ c * abs (g n)’
    (MP_TAC o Q.SPEC ‘n’)
 >> rw []
 >> ‘abs (k * f n) = abs k * abs (f n)’ by METIS_TAC [ABS_MUL]
 >> ‘0 < abs k’ by rw [ABS_NZ']
 >> ‘abs k * abs (f n) ≤ abs k * c * abs (g n)’ by simp [GSYM REAL_LE_LMUL]
 >> ‘abs k * c * abs (g n) = c * abs k * abs (g n)’ by rw [REAL_MUL_COMM]
 >> simp []
QED

Theorem BigO_SUM:
  ∀f g.
        (∀n. BigO (f n) (g n)) ⇒
         ∀n. BigO (λx. SIGMA (λi. f i x) (count n))
        (\x. SIGMA (λi. abs(g i x)) (count n))
Proof
    rw [BigO_def]
 >> fs[SKOLEM_THM]
 >> Cases_on ‘n’
 >- (simp[] \\
     Q.EXISTS_TAC ‘1’ \\
     simp[])
 >> Q.ABBREV_TAC ‘C = sup (IMAGE f' (count1 n'))’
 >> Q.ABBREV_TAC ‘N = MAX_SET (IMAGE f'' (count1 n'))’
 >> qexistsl_tac [‘C’, ‘N’]
 >> sg ‘0 < C’
    (* 0 < C *)
 >- (simp [Abbr ‘C’] \\
     MP_TAC (Q.SPECL [‘IMAGE f' (count1 n')’, ‘0’]
             REAL_LT_SUP_FINITE) \\
     rw [] \\
     Q.EXISTS_TAC ‘f' n'’ \\
     CONJ_ASM2_TAC
     >- (Q.EXISTS_TAC ‘n'’ \\
         simp []) \\
     simp [])
 >> simp []
 >> GEN_TAC
 >> STRIP_TAC
 >> (MP_TAC o (Q.SPECL [`λi. f i (x: num)`,`count1 n'`]) o
              (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_ABS_TRIANGLE
 >> rw [o_DEF]
 >> Know ‘∀n. n ≤ n' ⇒ f' n ≤ C’
 >- (rw [Abbr ‘C’] \\
     irule REAL_SUP_UBOUND_LE' \\
     simp [] \\
     qexists ‘REAL_SUM_IMAGE f' (count1 n')’ \\
     rw [] \\
     rename1 ‘i < SUC n'’ \\
     irule REAL_SUM_IMAGE_POS_MEM_LE \\
     simp [] \\
     GEN_TAC \\
     rw [] \\
     ‘0 < f' x'’ by METIS_TAC [] \\
     METIS_TAC [REAL_LT_IMP_LE])
 >> DISCH_TAC
 >> Know ‘∑ (λi. abs (C * abs (g i x))) (count1 n') = C * abs (∑ (λi. abs (g i x)) (count1 n'))’
 >- (‘∑ (λi. abs (C * abs (g i x))) (count1 n') =
      ∑ (λi. abs C * abs (abs (g i x))) (count1 n')’ by rw [ABS_MUL] \\
     ‘0 ≤ C’ by METIS_TAC [REAL_LT_IMP_LE] \\
     ‘abs C = C’ by rw [ABS_REFL] \\
     FULL_SIMP_TAC std_ss [] \\
     Know ‘∑ (λi. C * abs (abs (g i x))) (count1 n') =
           C * abs (∑ (λi. abs (g i x)) (count1 n'))’
     >- ((MP_TAC o (Q.SPECL [`count1 n'`]) o
                   (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_CMUL \\
         rw [] \\
         DISJ2_TAC \\
         (MP_TAC o (Q.SPECL [`λi. abs (g i (x: num))` ,`count1 n'`]) o
                   (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_POS \\
         rw []) \\
     DISCH_TAC \\
     METIS_TAC [REAL_LE_TRANS])
  >> DISCH_TAC
  >> MATCH_MP_TAC REAL_LE_TRANS
  >> Q.EXISTS_TAC ‘∑ (λi. abs (f i x)) (count1 n')’
  >> rw []
  >> POP_ASSUM (rw o wrap o SYM)
  >> irule REAL_SUM_IMAGE_MONO
  >> CONJ_TAC
  >- (Q.X_GEN_TAC ‘i’ \\
      BETA_TAC \\
      STRIP_TAC \\
      simp [] \\
      Q.PAT_X_ASSUM ‘∀n. 0 < f' n ∧ ∀n'. f'' n ≤ n' ⇒
                                         abs (f n n') ≤ f' n * abs (g n n')’
      (MP_TAC o Q.SPEC ‘i’) \\
      STRIP_TAC \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘x’) \\
      STRIP_TAC \\
      sg ‘f'' i ≤ x’
      >- (‘f'' i ≤ N’ by rw [Abbr ‘N’, in_max_set] \\
          METIS_TAC [LE_TRANS]) \\
      FULL_SIMP_TAC std_ss [] \\
      (* abs (f i x) ≤ abs (C * abs (g i x)) *)
      Know ‘f' i * abs (g i x) ≤ abs (C * abs (g i x))’
      >- (‘abs (C * abs (g i x)) = abs C * abs (g i x)’ by METIS_TAC [ABS_MUL, ABS_ABS] \\
          ‘0 ≤ C’ by METIS_TAC [REAL_LT_IMP_LE] \\
          ‘C = abs C’ by rw [abs] \\
          POP_ASSUM (rw o wrap o SYM) \\
          Know ‘f' i ≤ C’
          >- (‘i ≤ n'’ by  fs [count1_def] \\
              Q.PAT_X_ASSUM ‘∀n. n ≤ n' ⇒ f' n ≤ C’ (MP_TAC o (Q.SPEC ‘i’)) \\
              METIS_TAC [] \\
              simp []) \\
          DISCH_TAC \\
          Cases_on ‘abs (g i x) = 0’
          >- (METIS_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EQ_IMP_LE]) \\
          ‘0 ≤ abs (g i x)’ by METIS_TAC [ABS_POS]  \\
          ‘0 < abs (g i x)’ by METIS_TAC [REAL_LT_LE] \\
          simp [GSYM REAL_LE_LMUL]) \\
      METIS_TAC [REAL_LE_TRANS])
  >> simp []
QED

Theorem partial_sum_telescoping:
  ∀(X: num -> 'a -> real) Y (n:num) (j:num) x.
      1 ≤ j ∧ j ≤ n ∧
      j + 1 ≤ n ⇒
      ∀(Z: num -> 'a -> real). (∀j. Z j x = ∑ (λi. Y i x) {1 .. (j - 1)} +
                   ∑ (λi. X i x) {(j + 1) .. n}) ⇒
      Y j x + Z j x = X (j + 1) x + Z (j + 1) x
Proof
     rw []
 >> ‘Y j x + (∑ (λi. Y i x) {1 .. j − 1} + ∑ (λi. X i x) {j + 1 .. n}) =
     Y j x + ∑ (λi. Y i x) {1 .. j − 1} + ∑ (λi. X i x) {j + 1 .. n}’ by rw [REAL_ADD_ASSOC]
 >> POP_ORW
 >> simp []
 >> Know ‘Y j x + ∑ (λi. Y i x) {1 .. (j - 1)} = ∑ (λi. Y i x) {1 .. j}’
 >- (‘Y j x =  ∑ (λi. Y i x) {j}’ by rw[REAL_SUM_IMAGE_SING] \\
     (MP_TAC o (Q.SPECL [`{j}` ,`{1 .. j − 1}`]) o
               (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_DISJOINT_UNION \\
     impl_tac
     >- (CONJ_TAC
         >- (simp []) \\
         CONJ_TAC
         >- (simp [FINITE_NUMSEG]) \\
         simp [DISJOINT_NUMSEG]) \\
     DISCH_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘λi. Y i x’) \\
     STRIP_TAC \\
     ‘{j} ∪ {1 .. j − 1} = {1 .. j}’ by rw [Once EXTENSION] \\
     FULL_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> POP_ORW
 >> simp []
 >> ‘X (j + 1) x + (∑ (λi. Y i x) {1 .. j} + ∑ (λi. X i x) {j + 2 .. n}) =
     X (j + 1) x + ∑ (λi. Y i x) {1 .. j} + ∑ (λi. X i x) {j + 2 .. n}’ by rw [REAL_ADD_ASSOC]
 >> POP_ORW
 >> ‘X (j + 1) x + ∑ (λi. Y i x) {1 .. j} + ∑ (λi. X i x) {j + 2 .. n} =
     ∑ (λi. Y i x) {1 .. j} + X (j + 1) x  + ∑ (λi. X i x) {j + 2 .. n}’ by rw [REAL_ADD_COMM]
 >> Know ‘X (j + 1) x  + ∑ (λi. X i x) {j + 2 .. n} =  ∑ (λi. X i x) {j + 1 .. n}’
 >- (‘X (j + 1) x =  ∑ (λi. X i x) {j + 1}’ by rw[REAL_SUM_IMAGE_SING] \\
     (MP_TAC o (Q.SPECL [`{j + 1}` ,`{(j + 2) .. n}`]) o
               (INST_TYPE [alpha |-> ``:num``])) REAL_SUM_IMAGE_DISJOINT_UNION \\
     impl_tac
     >- (CONJ_TAC
         >- (simp []) \\
         CONJ_TAC
         >- (simp [FINITE_NUMSEG]) \\
         simp [DISJOINT_NUMSEG])\\
     DISCH_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘λi. X i x’) \\
     STRIP_TAC \\
     Know ‘{j + 1} ∪ {(j + 2) .. n} = {j + 1 .. n}’
     >- (‘j + 1 ≤ j + 2’ by RW_TAC arith_ss [] \\
         (MP_TAC o (Q.SPECL [`j + 1` ,`j + 1`, `n - (j + 1)`]) o
                   (INST_TYPE [alpha |-> ``:num``])) NUMSEG_ADD_SPLIT \\
         simp [] \\
         ‘{j + 1 .. j + 1} =  {j + 1}’ by rw [NUMSEG_SING] \\
         RW_TAC arith_ss [GSYM NUMSEG_LREC, SUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] \\
         ‘j + 1 + (n − (j + 1)) = n’ by RW_TAC arith_ss [LESS_EQ_ADD_SUB] \\
         simp []) \\
     DISCH_TAC \\
     FULL_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> POP_ASSUM (rw o wrap o SYM)
 >> simp [REAL_ADD_ASSOC]
QED

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
 >- (METIS_TAC [])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘h’, ‘λx. Normal z * h x’, ‘z’]
            IN_MEASURABLE_BOREL_CMUL)
 >> impl_tac
 >- (METIS_TAC [])
 >> ‘!x. x IN space a ==> (Normal z * h x = g x)’ by rw [Abbr ‘h’]
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘g’, ‘λx. Normal z * h x’]
            IN_MEASURABLE_BOREL_EQ')
 >> impl_tac
 >> BETA_TAC
 >- (METIS_TAC [])
 >> simp []
QED

Theorem real_to_extreal_rv[local]:
    ∀p X. prob_space p ∧ random_variable X p borel ⇒
          real_random_variable (Normal o X) p
Proof
    rw [real_random_variable_def, random_variable_def]
 >> irule IN_MEASURABLE_BOREL_IMP_BOREL'
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
QED

Theorem extreal_to_real_rv[local]:
    ∀p X. prob_space p ∧
        real_random_variable (Normal o X) p ⇒
        random_variable X p borel
Proof
    rw [real_random_variable_def, random_variable_def]
 >> MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘Normal o X’]
            in_borel_measurable_from_Borel)
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
 >> rw [o_DEF]
 >> METIS_TAC []
QED

Theorem real_random_variable_equiv:
  ∀p X. prob_space p ⇒
        (real_random_variable (Normal o X) p ⇔
        random_variable X p borel)
Proof
    rw [real_random_variable_def, random_variable_def,
        AND_INTRO_THM, EQ_IMP_THM]
 >- (MP_TAC (Q.SPECL [‘(p_space p,events p)’, ‘Normal o X’]
             in_borel_measurable_from_Borel) \\
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def,
                           p_space_def, events_def, measure_space_def] \\
     rw [o_DEF] \\
     METIS_TAC [])
 >> irule IN_MEASURABLE_BOREL_IMP_BOREL'
 >> FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, prob_space_def, p_space_def, events_def, measure_space_def]
QED

(* ------------------------------------------------------------------------- *)
(*  Expectation                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem expectation_add:
  ∀p X Y.
          prob_space p ∧
          real_random_variable X p ∧
          integrable p X ∧
          real_random_variable Y p ∧
          integrable p Y ⇒
          expectation p (λx. X x + Y x) = expectation p X + expectation p Y
Proof
    rw [expectation_def, prob_space_def, real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC integral_add
 >> simp []
QED

Theorem expectation_add':
  ∀p X Y.
          prob_space p ∧
          random_variable X p borel ∧
          integrable p (Normal o X) ∧
          random_variable Y p borel ∧
          integrable p (Normal o Y) ⇒
          expectation p (Normal o (λx. X x + Y x)) =
          expectation p (Normal o X) + expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_add)
 >> simp []
 >> STRIP_TAC
 >> Know ‘expectation p (λx. Normal (X x) + Normal (Y x)) =
          expectation p (Normal ∘ (λx. X x + Y x))’
 >- (MATCH_MP_TAC expectation_cong \\
     rw[extreal_add_eq])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [integrable_def]
 >> ‘real_random_variable (Normal ∘ X) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> ‘real_random_variable (Normal ∘ Y) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem expectation_sub:
  ∀p X Y.
          prob_space p ∧
          real_random_variable X p ∧
          integrable p X ∧
          real_random_variable Y p ∧
          integrable p Y ⇒
          expectation p (λx. X x - Y x) = expectation p X - expectation p Y
Proof
    rw [expectation_def, prob_space_def, real_random_variable_def, p_space_def]
 >> MATCH_MP_TAC integral_sub
 >> simp []
QED

Theorem expectation_sub':
  ∀p X Y.
          prob_space p ∧
          random_variable X p borel ∧
          integrable p (Normal o X) ∧
          random_variable Y p borel ∧
          integrable p (Normal o Y) ⇒
          expectation p (Normal o (λx. X x - Y x)) =
          expectation p (Normal o X) - expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_sub)
 >> simp []
 >> STRIP_TAC
 >> Know ‘expectation p (λx. Normal (X x) - Normal (Y x)) =
          expectation p (Normal ∘ (λx. X x - Y x))’
 >- (MATCH_MP_TAC expectation_cong \\
     rw[extreal_sub_eq])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [integrable_def]
 >> ‘real_random_variable (Normal ∘ X) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> ‘real_random_variable (Normal ∘ Y) p’
     by rw [real_random_variable_def, random_variable_def, p_space_def, events_def]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem expectation_mono:
    ∀p X Y.
            prob_space p ∧
            real_random_variable X p ∧
            integrable p X ∧
            real_random_variable Y p ∧
            integrable p Y ∧
            (∀x. x IN p_space p ⇒ X x ≤ Y x) ⇒
            expectation p X ≤ expectation p Y
Proof
    rw []
 >> Q.ABBREV_TAC ‘Z = λx. Y x - X x’
 >> ‘∀x. x IN p_space p ⇒ Z x = Y x - X x’ by rw [Abbr ‘Z’]
 >> ‘real_random_variable Z p’ by rw [Abbr ‘Z’, real_random_variable_sub]
 >> Know ‘∀x. x IN p_space p ⇒ 0 ≤ Z x’
 >- (fs [Abbr ‘Z’, real_random_variable_def] \\
     METIS_TAC [sub_zero_le])
 >> DISCH_TAC
 >> Know ‘integrable p Z’
 >- (fs [Abbr ‘Z’] \\
     MP_TAC (Q.SPECL [‘p’, ‘Y’, ‘X’]
             integrable_sub') \\
     fs [prob_space_def])
 >> DISCH_TAC
 >> Know ‘0 ≤ expectation p Z’
 >- (irule expectation_pos \\
     simp [])
 >> DISCH_TAC
 >> Know ‘∀x. x IN p_space p ⇒ Z x + X x = Y x’
 >- (fs [Abbr ‘Z’, real_random_variable_def] \\
     GEN_TAC \\
     STRIP_TAC \\
     METIS_TAC [sub_add])
 >> DISCH_TAC
 >> Know ‘expectation p (λx. Z x + X x) =
          expectation p (λx. Y x)’
 >- (MATCH_MP_TAC expectation_cong \\
     rw [])
 >> DISCH_TAC
 >> Know ‘expectation p (λx. Z x + X x) =
          expectation p Z + expectation p X’
 >- (MATCH_MP_TAC expectation_add \\
     simp [])
 >> rpt STRIP_TAC
 >> ‘expectation p (λx. Y x) =
     expectation p Z + expectation p X’ by fs []
 >> ‘expectation p (λx. Y x) = expectation p Y’ by METIS_TAC []
 >> FULL_SIMP_TAC std_ss []
 >> POP_ORW
 >> ‘expectation p X ≠ PosInf ∧ expectation p X ≠ NegInf’
    by METIS_TAC [expectation_finite]
 >> ‘expectation p Z ≠ PosInf ∧ expectation p Z ≠ NegInf’
    by METIS_TAC [expectation_finite]
 >> ‘expectation p Z + expectation p X =
     expectation p X + expectation p Z’ by METIS_TAC [add_comm]
 >> POP_ORW
 >> METIS_TAC [le_addr_imp]
QED

Theorem expectation_mono':
    ∀p X Y.
            prob_space p ∧
            random_variable X p borel ∧
            integrable p (Normal o X) ∧
            random_variable Y p borel ∧
            integrable p (Normal o Y) ∧
            (∀x. X x ≤ Y x) ⇒
            expectation p (Normal o X) ≤ expectation p (Normal o Y)
Proof
    rw []
 >> MP_TAC (Q.SPECL [‘p’, ‘Normal o X’, ‘Normal o Y’]
            expectation_mono)
 >> fs []
 >> STRIP_TAC
 >> ‘real_random_variable (Normal ∘ X) p’ by METIS_TAC [real_to_extreal_rv]
 >> ‘real_random_variable (Normal ∘ Y) p’ by METIS_TAC [real_to_extreal_rv]
 >> fs []
QED

Theorem expectation_mono_alt:
    ∀p f g.
            prob_space p ∧ integrable p f ∧ integrable p g ∧
            (∀x. x ∈ p_space p ⇒ f x ≤ g x) ⇒
            expectation p f ≤ expectation p g
Proof
  rw [prob_space_def, p_space_def, expectation_def]
  >> MATCH_MP_TAC integral_mono >> art []
QED

(* ------------------------------------------------------------------------- *)
(*  Taylor Theorem                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem TAYLOR_REMAINDER:
  ∀(diff :num -> real -> real) (n :num) x.
                          ∃(M :extreal) t.
                                           abs (Normal (diff n t)) ≤ M ⇒
                                           abs (Normal ((diff n t / ((&FACT n) :real))) * Normal x pow n) ≤
                                           M / (Normal (&FACT n)) * abs (Normal x) pow n
Proof
    rpt GEN_TAC
 >> qexistsl [‘M’, ‘t’]
 >> STRIP_TAC
 >> ‘Normal x pow n = Normal (x pow n)’ by rw [extreal_pow_def]
 >> POP_ORW
 >> ‘abs (Normal x) = Normal (abs x)’ by METIS_TAC [extreal_abs_def]
 >> POP_ORW
 >> ‘Normal (abs x) pow n = Normal ((abs x) pow n)’ by rw [extreal_pow_def]
 >> POP_ORW
 >> ‘abs x pow n = abs (x pow n)’ by rw [POW_ABS]
 >> POP_ORW
 >> Cases_on ‘x pow n = 0’
 >- (‘abs (Normal (diff n t / &FACT n) * Normal (x pow n)) = 0’
      by METIS_TAC [normal_0, mul_rzero, abs_0] \\
     ‘M / Normal (&FACT n) * Normal (abs (x pow n)) = 0’
      by METIS_TAC [ABS_0, normal_0, mul_rzero] \\
     simp [])
 >> Know ‘!n. (0: real) < &FACT n’
 >- (EVAL_TAC \\
     rw [FACT_LESS, LE_1])
 >> DISCH_TAC
 >> ‘∀n. (0: real) <= &FACT n’ by METIS_TAC [REAL_LT_IMP_LE]
 >> ‘∀n. (0: real) ≠ &FACT n’ by METIS_TAC [REAL_LT_IMP_NE]
 >> Know ‘0 ≤ M’
 >- (simp [sup_le] \\
     rw [le_sup] \\
     METIS_TAC [abs_pos, le_trans])
 >> DISCH_TAC
 >> ‘NegInf ≠ M’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> Cases_on ‘M = PosInf’
 >- (‘M / Normal (&FACT n) = PosInf’ by METIS_TAC [infty_div] \\
     ‘0 < Normal (abs (x pow n))’ by rw [abs_gt_0] \\
     ‘M / Normal (&FACT n) * Normal (abs (x pow n)) = PosInf’ by METIS_TAC [mul_infty] \\
     rw [])
 >> ‘∃r. M = Normal r’ by METIS_TAC [extreal_cases]
 >> rw []
 >> ‘Normal (diff n t / &FACT n) * Normal (x pow n) =
     Normal (diff n t / &FACT n * x pow n)’ by METIS_TAC [extreal_mul_def]
 >> POP_ORW
 >> ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’ by METIS_TAC [extreal_div_eq]
 >> POP_ORW
 >> ‘Normal (r / &FACT n) * Normal (abs (x pow n)) =
     Normal (r / &FACT n * abs (x pow n))’ by METIS_TAC [extreal_mul_def]
 >> POP_ORW
 >> ‘abs (Normal (diff n t / &FACT n * x pow n)) =
     Normal (abs (diff n t / &FACT n * x pow n))’ by METIS_TAC [extreal_abs_def]
 >> POP_ORW
 >> ‘abs (Normal (diff n t)) = Normal (abs (diff n t))’ by METIS_TAC [extreal_abs_def]
 >> FULL_SIMP_TAC std_ss [extreal_le_eq]
 >> ‘abs (diff n t) / &FACT n ≤ r / &FACT n’ by rw [REAL_LE_RDIV_CANCEL]
 >> ‘abs (&FACT n) = (&FACT n: real)’ by rw [ABS_REFL]
 >> ‘abs (diff n t) / &FACT n = abs (diff n t / &FACT n)’ by METIS_TAC [GSYM ABS_DIV]
 >> FULL_SIMP_TAC std_ss []
 >> ‘0 < abs (x pow n)’ by METIS_TAC [ABS_NZ]
 >> ‘abs (diff n t / &FACT n) * abs (x pow n) ≤ r / &FACT n * abs (x pow n)’
     by METIS_TAC [GSYM REAL_LE_RMUL]
 >> ‘abs (diff n t / &FACT n) * abs (x pow n) = abs (diff n t / &FACT n * x pow n)’
     by METIS_TAC [GSYM ABS_MUL]
 >> FULL_SIMP_TAC std_ss []
QED

Theorem TAYLOR_REMAINDER':
  ∀(diff:num -> real -> real) n (x:real).
    ∃M t.
          abs (diff n t) ≤ M ⇒
          abs (diff n t / (&FACT n:real) * x pow n) ≤
          M / &FACT n * abs (x) pow n
Proof
    rpt GEN_TAC
    >> qexistsl [‘M’, ‘t’]
    >> STRIP_TAC
    >> ‘diff n t / &FACT n = diff n t * (&FACT n)⁻¹’ by METIS_TAC [real_div]
    >> POP_ORW
    >> ‘M / &FACT n =  M * (&FACT n)⁻¹’ by METIS_TAC [real_div]
    >> POP_ORW
    >> ‘!n. &0 < (&FACT n:real)’ by rw [REAL_LT, FACT_LESS]
    >> POP_ASSUM (MP_TAC o Q.SPEC ‘n’)
    >> DISCH_TAC
    >> ‘0 <= (&FACT n: real)’ by METIS_TAC [REAL_LT_IMP_LE]
    >> ‘&0 < (inv(&FACT n):real)’ by  METIS_TAC [REAL_INV_POS]
    >> ‘abs (diff n t) * inv(&FACT n) ≤ M  * inv(&FACT n)’ by
        METIS_TAC [REAL_LE_RMUL]
    >> ‘abs (inv(&FACT n:real)) = inv(&FACT n)’ by rw[ABS_REFL]
    >> ‘abs (diff n t) * abs (&FACT n)⁻¹ = abs (diff n t) * (&FACT n)⁻¹’ by rw []
    >> ‘abs (diff n t) * abs (&FACT n)⁻¹ = abs (diff n t * (&FACT n)⁻¹)’ by METIS_TAC [ABS_MUL]
    >> ‘abs (diff n t * (&FACT n)⁻¹) ≤ M  * inv(&FACT n)’ by METIS_TAC []
    >> ‘0 ≤ abs (x pow n)’ by METIS_TAC [REAL_ABS_POS]
    >> Cases_on ‘x pow n = 0’
    >- (‘x = 0’ by METIS_TAC [POW_ZERO] \\
        ‘abs x pow n = abs (x pow n)’ by rw [POW_ABS] \\
        ‘abs (x pow n) = 0’ by METIS_TAC [REAL_ABS_0] \\
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
 >> ‘∀x. g x = f (x + a)’ by rw [Abbr ‘g’]
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘x - a’)
 >> ‘f (x - a + a) = f x’ by METIS_TAC [REAL_SUB_ADD]
 >> POP_ORW
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘diff' = \n x. diff n (x + a)’
 >> MP_TAC (Q.SPECL [‘g’, ‘diff'’, ‘x - a’, ‘n’] MCLAURIN)
 >> impl_tac
 >- (CONJ_TAC
    (* 0 < x − a *)
     >- (rw [REAL_SUB_LT])
     >> CONJ_TAC
    (* 0 < n *)
     >> fs []
     >> CONJ_TAC
    (* diff' 0 = g *)
     >- (rw [Abbr ‘diff'’])
     (* ∀m t. m < n ∧ 0 ≤ t ∧ t ≤ x − a ⇒ (diff' m diffl diff' (SUC m) t) t *)
     >> Q.UNABBREV_TAC ‘diff'’
     >> BETA_TAC
     >> qx_genl_tac [‘m’, ‘t’]
     >> STRIP_TAC
     >> ‘a ≤ t + a’ by rw [REAL_LE_ADDL]
     >> ‘t + a ≤ x’ by METIS_TAC [REAL_LE_SUB_LADD]
     >> Q.PAT_X_ASSUM ‘∀m t. m < n ∧ a ≤ t ∧ t ≤ x ⇒
                             (diff m diffl diff (SUC m) t) t’
       (MP_TAC o Q.SPECL [‘m’, ‘t + a’])
     >> DISCH_TAC
     >> MP_TAC (Q.SPECL [‘diff (m:num)’, ‘λx. (x + a)’, ‘diff (SUC m) (t + a:real)’, ‘1’, ‘t’] limTheory.DIFF_CHAIN)
     >> impl_tac
     >- (CONJ_TAC
         >- (BETA_TAC \\
             METIS_TAC [])
         (* ((λx. x + a) diffl 1) t *)
         >> Know ‘((λx. x + a) diffl (1 + 0)) t’
         >- (MP_TAC (Q.SPECL [‘λx. x’, ‘λx. a’, ‘1’, ‘0’, ‘t’] limTheory.DIFF_ADD) \\
             impl_tac \\
             METIS_TAC [limTheory.DIFF_X, limTheory.DIFF_CONST] \\
             BETA_TAC \\
             simp [])
         >> simp [REAL_ADD_RID])
         >> simp [])
 >> simp[]
 >> DISCH_THEN (Q.X_CHOOSE_TAC ‘t’)
 >> Q.EXISTS_TAC ‘t + a’
 >> CONJ_TAC
 >- (rw [REAL_LT_ADDL])
 >> CONJ_TAC
 >- (rw [REAL_LT_ADD_SUB])
 >> Know ‘∀m. diff' m 0 = diff m a’
    >- (Q.UNABBREV_TAC ‘diff'’ \\
        BETA_TAC \\
        simp [])
 >> DISCH_TAC
 >> simp []
QED

Theorem TAYLOR_CLT_LEMMA[local]:
    ∀diff (f:real -> real) x y.
          0 < y ∧ diff (0:num) = f ∧
          (∀m t.  m < 3 ∧ x ≤ t ∧ t ≤ x + y ⇒ (diff m diffl diff (SUC m) t) t) ∧
            (∃z. ∀x. abs (diff 3 x) ≤ z) ⇒
                     abs (f (x + y) - (f x + diff 1 x * y + diff 2 x / 2 * y pow 2)) ≤
                     sup {abs (diff 3 x) | x | T} / 6 * abs y pow 3
Proof
    rpt GEN_TAC
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘diff’, ‘x’, ‘x + y’, ‘3’] TAYLOR_THEOREM)
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘t’ STRIP_ASSUME_TAC)
 >> ‘x + y − x = y’ by rw [REAL_ADD_SUB]
 >> FULL_SIMP_TAC std_ss []
 >> Know ‘sum (0,3) (λm. diff m x / &FACT m * y pow m) =
           (f x + diff 1 x * y + diff 2 x / 2 * y²)’
 >- (EVAL_TAC \\
     simp [])
 >> fs []
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘Z = f x + diff 1 x * y + diff 2 x / 2 * y²’
 >> fs []
 >> ‘Z + y³ * (&FACT 3)⁻¹ * diff 3 t − Z = y³ * (&FACT 3)⁻¹ * diff 3 t’ by rw [REAL_ADD_SUB]
 >> POP_ORW
 >> Q.UNABBREV_TAC ‘Z’
 >> ‘inv(&FACT 3) = (inv(6):real)’ by EVAL_TAC
 >> POP_ORW
 >> simp []
 >> ‘abs (1 / 6 * (y³ * diff 3 t)) = abs (1/6) * abs (y³ * diff 3 t)’ by rw [ABS_MUL]
 >> POP_ORW
 >> ‘6 * (abs (1 / 6) * abs (y³ * diff 3 t)) = abs (y³ * diff 3 t)’
     by rw [GSYM REAL_MUL_ASSOC, ABS_REFL, REAL_MUL_RINV, REAL_MUL_RID]
 >> POP_ORW
 >> ‘abs (y³ * diff 3 t) = abs (y³) * abs (diff 3 t)’ by rw [ABS_MUL]
 >> POP_ORW
 >> ‘abs (y pow 3) = abs y pow 3’ by METIS_TAC [POW_ABS]
 >> POP_ORW
 >> MATCH_MP_TAC REAL_LE_LMUL1
 >> CONJ_TAC
 >- (METIS_TAC [ABS_POS, POW_POS])
 >> irule REAL_SUP_UBOUND_LE
 >> CONJ_TAC
 >- (ONCE_REWRITE_TAC [GSYM SPECIFICATION]\\
     simp [] \\
     qexists ‘t’ \\
     rw [])
 >> CONJ_TAC
 >- (qexists ‘abs (diff 3 0)’ \\
     ONCE_REWRITE_TAC [GSYM SPECIFICATION]\\
     simp [] \\
     qexists ‘0’ \\
     rw [])
 >> qexists ‘z’
 >> GEN_TAC
 >> Know ‘{abs (diff 3 x) | x | T} x' ⇔ x' IN {abs (diff 3 x) | x | T}’
 >- (REWRITE_TAC [SPECIFICATION]) >> Rewr'
 >> simp []
 >> STRIP_TAC
 >> rw []
QED

Theorem real_random_variable_abs:
    ∀p X.
          prob_space p ∧ real_random_variable X p ⇒
          real_random_variable (λx. abs (X x)) p
Proof
    rpt STRIP_TAC
 >> fs [real_random_variable, prob_space_def, p_space_def, events_def]
 >> CONJ_TAC
 (* (λx. abs (X x)) ∈ Borel_measurable (measurable_space p) *)
 >- (irule IN_MEASURABLE_BOREL_ABS \\
     FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA_BOREL, measure_space_def] \\
     qexists ‘X’ \\
     simp [])
 (* ∀x. x ∈ m_space p ⇒ abs (X x) ≠ −∞ ∧ abs (X x) ≠ +∞ *)
 >> Q.X_GEN_TAC ‘x’
 >> DISCH_TAC
 >> ‘?z. X x = Normal z’ by METIS_TAC [extreal_cases] >> POP_ORW
 >> rw[extreal_abs_def]
QED

Theorem in_borel_measurable_pow:
    !a n f g. sigma_algebra a /\
              f IN measurable a borel /\
              (!x. x IN space a ==> (g x = (f x) pow n)) ==>
                   g IN measurable a borel
Proof
    STRIP_TAC
 >> Induct_on ‘n’
 >- (FULL_SIMP_TAC std_ss [pow0] \\
     METIS_TAC [in_borel_measurable_const])
 >> rpt STRIP_TAC
 >> fs [real_pow]
 >> irule in_borel_measurable_mul
 >> simp []
 >> qexistsl [‘f’, ‘λx. f x pow n’]
 >> simp []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> qexists ‘f’
 >> simp []
QED

Theorem TAYLOR_REMAINDER_EXPECTATION:
    ∀p diff n X.
                 prob_space p ∧ random_variable X p borel ∧
                 integrable p (Normal o X) ∧
                 integrable p (λx. Normal (X x pow n)) ⇒
                 ∃M (t: real).
                               abs (Normal (diff n t)) ≤ M ⇒
                               expectation p (λx. abs (Normal (diff n t / &FACT n) * (Normal ∘ X) x pow n)) ≤
                               M / Normal (&FACT n) * expectation p (λx. abs ((Normal ∘ X) x) pow n)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘diff’, ‘n’, ‘X x’]
            TAYLOR_REMAINDER)
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘M’
               (Q.X_CHOOSE_THEN ‘t’ ASSUME_TAC))
 >> qexistsl [‘M’, ‘t’]
 >> STRIP_TAC
 >> fs [o_DEF]
 >> Know ‘integrable p (λx'. abs (Normal (X x' pow n)))’
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx. Normal (X x pow n)’]
             integrable_abs) \\
     FULL_SIMP_TAC std_ss [prob_space_def, o_DEF])
 >> DISCH_TAC
 >> ‘∀x'. abs (Normal (X x')) pow n = abs (Normal (X x') pow n)’
    by rw [extreal_abs_def, extreal_pow_def, POW_ABS]
 >> rw []
 >> ‘∀x'. Normal (X x') pow n = Normal ((X x') pow n)’ by rw [extreal_pow_def]
 >> rw []
 >> Cases_on ‘expectation p (λx'. abs (Normal (X x' pow n))) = 0’
 >- (rw [] \\
     Q.ABBREV_TAC ‘c = diff n t / &FACT n’ \\
     ‘∀x'. abs (Normal c * Normal (X x' pow n)) =
           abs (Normal c) * abs (Normal (X x' pow n))’ by rw [abs_mul] \\
     POP_ORW \\
     ‘abs (Normal c) = Normal (abs c)’ by rw [extreal_abs_def] \\
     POP_ORW \\
     ‘expectation p (λx'. Normal (abs c) * abs (Normal (X x' pow n)))  =
      Normal (abs c) * expectation p (λx'. abs (Normal (X x' pow n)))’
     by METIS_TAC [expectation_cmul] \\
     POP_ORW \\
     Q.PAT_X_ASSUM ‘expectation p (λx'. abs (Normal (X x' pow n))) = 0’ MP_TAC \\
     rw [])
 >> Know ‘0 ≤ M’
 >- (simp [sup_le] \\
     rw [le_sup] \\
     METIS_TAC [abs_pos, le_trans])
 >> DISCH_TAC
 >> ‘M ≠ NegInf’ by METIS_TAC [extreal_0_simps, lt_trans]
 >> Know ‘!n. (0: real) < &FACT n’
 >- (EVAL_TAC \\
     rw [FACT_LESS, LE_1])
 >> DISCH_TAC
 >> ‘∀n. (0: real) <= &FACT n’ by METIS_TAC [REAL_LT_IMP_LE]
 >> ‘∀n. (0: real) ≠ &FACT n’ by METIS_TAC [REAL_LT_IMP_NE]
 >> ‘∀x'. abs (Normal (X x')) pow n = abs (Normal (X x') pow n)’
     by rw [extreal_abs_def, extreal_pow_def, POW_ABS]
 >> rw []
 >> Cases_on ‘∀x'. Normal (X x' pow n) = 0’
 >- (rw [abs_0, expectation_zero])
 >> FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
 >> Cases_on ‘M = PosInf’
 >- (Know ‘M / Normal (&FACT n) * expectation p (λx'. abs (Normal (X x' pow n))) = PosInf’
     >- (‘M / Normal (&FACT n) = PosInf’ by METIS_TAC [infty_div] \\
         POP_ORW \\
         MATCH_MP_TAC (cj 1 mul_infty) \\
         ‘∀x'. 0 ≤ abs (Normal (X x' pow n))’ by METIS_TAC [abs_pos] \\
         Know ‘0 ≤ expectation p (λx'. abs (Normal (X x' pow n)))’
         >- (irule expectation_pos \\
             simp []) \\
         DISCH_TAC \\
         simp [lt_le]) \\
     DISCH_TAC \\
     rw [])
 >> ‘∃r. M = Normal r’ by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss []
 >> ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’ by METIS_TAC [extreal_div_eq]
 >> POP_ORW
 >> Know ‘expectation p (λx'. Normal (r / &FACT n) * abs (Normal (X x' pow n))) =
          Normal (r / &FACT n) * expectation p (λx'. abs (Normal (X x' pow n)))’
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x' pow n))’, ‘r / &FACT n’]
             expectation_cmul) \\
     simp [])
 >> DISCH_TAC
 >> POP_ASSUM (rw o wrap o SYM)
 >> irule expectation_mono
 >> BETA_TAC
 >> simp []
 >> CONJ_TAC
  (* ∀x. x ∈ p_space p ⇒
         abs (Normal (diff n t / &FACT n) * Normal (X x pow n)) ≤
         Normal (r / &FACT n) * abs (Normal (X x pow n)) *)
 >- (GEN_TAC \\
     STRIP_TAC \\
     ‘abs (Normal (diff n t / &FACT n) * Normal (X x'' pow n)) =
      abs (Normal (diff n t / &FACT n)) * abs (Normal (X x'' pow n))’ by rw [abs_mul] \\
     POP_ORW \\
     irule le_rmul_imp \\
     simp [abs_pos] \\
     ‘abs (Normal (diff n t / &FACT n)) =
      abs (Normal (diff n t) / Normal (&FACT n))’ by METIS_TAC [extreal_div_eq] \\
     POP_ORW \\
     Know ‘abs (Normal (diff n t) / Normal (&FACT n)) =
           abs (Normal (diff n t)) / abs (Normal (&FACT n))’
     >- (irule abs_div \\
         simp [extreal_not_infty]) \\
     Rewr' \\
     ‘abs (Normal (&FACT n)) = Normal (&FACT n)’ by rw [abs_refl] \\
     POP_ORW \\
     ‘Normal r / Normal (&FACT n) = Normal (r / &FACT n)’
     by METIS_TAC [extreal_div_eq] \\
     POP_ASSUM (rw o wrap o SYM) \\
     irule ldiv_le_imp \\
     simp [cj 2 extreal_not_infty])
 >> CONJ_TAC
  (* integrable p
          (λx'. abs (Normal (diff n t / &FACT n) * Normal (X x' pow n))) *)
 >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. Normal ((diff : num -> real -> real) n (t : real) / &FACT n) *
                                 Normal (X x' pow n)’]
             integrable_abs) \\
     fs [prob_space_def] \\
     impl_tac
      (* integrable p (λx'. Normal (diff n t / &FACT n) * Normal (X x' pow n)) *)
     >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. Normal (X x' pow n)’,
                          ‘(diff : num -> real -> real) n (t : real) / &FACT n’]
                 integrable_cmul) \\
     simp [] \\
     impl_tac \\
     simp [o_DEF]) \\
     simp [o_DEF])
 >> CONJ_TAC
  (* integrable p (λx'. Normal (r / &FACT n) * abs (Normal (X x' pow n))) *)
    >- (MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x' pow n))’,
                       ‘r / &FACT n’]
                integrable_cmul) \\
        fs [o_DEF, prob_space_def])
    >> Know ‘(λx'. (X x') pow n) ∈ borel_measurable (measurable_space p)’
    >- (irule in_borel_measurable_pow \\
        fs [SIGMA_ALGEBRA_BOREL, prob_space_def] \\
        qexistsl_tac [‘X’, ‘n’] \\
        fs [random_variable_def, p_space_def, events_def] \\
        METIS_TAC [])
    >> DISCH_TAC
 >> CONJ_TAC
  (* real_random_variable
          (λx'. abs (Normal (diff n t / &FACT n) * Normal (X x' pow n))) p *)
 >- (Q.ABBREV_TAC ‘c = diff n t / &FACT n’ \\
     MP_TAC (Q.SPECL [‘p’, ‘λx'. Normal c * Normal (X x' pow n)’]
             real_random_variable_abs) \\
     simp [] \\
     Know ‘real_random_variable (λx. Normal (X x pow n)) p’
     >- (fs [real_random_variable_def, random_variable_def, p_space_def,
             events_def, extreal_not_infty, abs_not_infty] \\
         METIS_TAC [IN_MEASURABLE_BOREL_IMP_BOREL]) \\
     DISCH_TAC \\
     MP_TAC (Q.SPECL [‘p’, ‘λx. Normal (X x pow n)’, ‘c’]
             real_random_variable_cmul) \\
     simp [])
  (* real_random_variable
          (λx'. Normal (r / &FACT n) * abs (Normal (X x' pow n))) p *)
 >> Know ‘real_random_variable (λx'. Normal (X x' pow n)) p’
 >- (fs [real_random_variable_def, random_variable_def, p_space_def, events_def] \\
     METIS_TAC [IN_MEASURABLE_BOREL_IMP_BOREL])
 >> DISCH_TAC
 >> Know ‘real_random_variable (λx''. abs (Normal (X x'' pow n))) p’
 >- (fs [real_random_variable_def, random_variable_def, p_space_def,
         events_def, extreal_not_infty, abs_not_infty] \\
     MP_TAC (Q.SPECL [‘measurable_space p’, ‘λx'. Normal (X x' pow n)’]
             IN_MEASURABLE_BOREL_ABS') \\
     fs [SIGMA_ALGEBRA_BOREL, prob_space_def, o_DEF])
 >> MP_TAC (Q.SPECL [‘p’, ‘λx'. abs (Normal (X x')) pow n’,
                     ‘r / &FACT n’]
            real_random_variable_cmul)
 >> simp []
QED

Theorem taylor_thm[local]:
    ∀(diff :num -> real -> real) x n.
                   sup {abs (Normal (diff n x)) | x | T} ≠ NegInf
Proof
    rw []
 >> ‘∀x. Normal (diff n x) ≠ NegInf ∧
         Normal (diff n x) ≠ PosInf’ by rw [extreal_not_infty]
 >> ‘∀x. abs (Normal (diff n x)) ≠ NegInf ∧
         abs (Normal (diff n x)) ≠ PosInf’ by rw [abs_not_infty]
 >> ‘∀x. 0 ≤ abs (Normal (diff n x))’ by METIS_TAC [abs_pos]
 >> MP_TAC (Q.SPECL [‘{abs (Normal ((diff :num -> real -> real) n x)) | x | T}’, ‘0’]
            le_sup_imp2)
 >> simp []
 >> METIS_TAC [extreal_0_simps, lt_trans]
QED

Definition third_moment_def:
  third_moment p X = central_moment p X 3
End

Theorem taylor_clt_tactic1[local]:
    ∀p X Y (diff :num -> real -> real) n f.
            prob_space p ∧
            random_variable X p borel ∧
            random_variable Y p borel ∧
            bounded (IMAGE f 𝕌(:real)) ∧
            f continuous_on 𝕌(:real) ∧
            diff 0 = f ∧
            indep_vars p Y X borel borel ⇒
            indep_vars p (λx. (diff n (Y x))) (λx. X x pow n) borel borel
Proof
    rw []
 >> cheat
QED

Definition diff_def :
    (diff 0       f x = f x) /\
    (diff (SUC m) f x = @y. ((diff m f) diffl y)(x))
End

Theorem diff_thm :
    !f. (!m t. ?x. (diff m f diffl x) t) ==>
        (diff 0 f = f) /\
        (!m t. ((diff m f) diffl (diff (SUC m) f t))(t))
Proof
    rw [diff_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> simp []
QED

(*
Definition higher_differentiable_def:
  higher_differentiable 0 f x ⇔ T ∧
  (∀n. higher_differentiable (SUC n) f x ⇔ higher_differentiable n f x ∧ ∃l. (diff n f diffl l) x)
End

Theorem higher_differentiable_diff:
  ∀f (n: num) x. higher_differentiable n f x ⇒ ∃l. (diff n f diffl l) x
Proof
  Induct_on `n` >> rw [higher_differentiable_def, diff_def]
  >> METIS_TAC []
QED
*)

Theorem in_borel_measurable_diff:
    ∀a f g diff.
       sigma_algebra a ∧ f ∈ borel_measurable a ∧ diff 0 = f ∧
       (∀x. x ∈ space a ⇒ g x = diff 1 (f x)) ⇒
       g ∈ borel_measurable a
Proof
  cheat
QED

(*
Theorem TAYLOR_CLT_EXPECTATION[local]:
    ∀p X Y (diff :num -> real -> real) f.
            prob_space p ∧
            random_variable X p borel ∧
            random_variable Y p borel ∧
            integrable p (Normal ∘ X) ∧
            integrable p (Normal ∘ Y) ∧
            integrable p (λx. Normal (X x pow 3)) ∧
            third_moment p (Normal ∘ X) < +∞ ∧
            diff 0 = f ∧
            bounded (IMAGE f 𝕌(:real)) ∧
            f continuous_on 𝕌(:real) ∧
            (∀m t x. m < 3 ∧ Y x ≤ t ∧ t ≤ Y x + abs (X x) ⇒ (diff m diffl diff (SUC m) t) t) ∧
            (∃z. ∀x. abs (diff 3 x) ≤ z) ⇒
            abs (expectation p (Normal ∘ f ∘ (λx. Y x + X x)) −
            (expectation p (Normal ∘ f ∘ (λx. Y x)) +
            expectation p (λx. Normal (diff 1 (Y x))) *
            expectation p (Normal ∘ (λx. X x)) +
            1 / 2 * expectation p (λx. Normal (diff 2 (Y x))) *
            expectation p (Normal ∘ (λx. X x pow 2)))) ≤
            sup {abs (Normal (diff 3 x)) | x | T} / 6 * expectation p (abs ∘ Normal ∘ (λx. (X x)³))
Proof
    rpt STRIP_TAC
 >> Cases_on ‘∀x. X x = 0’
 >- (simp [o_DEF, normal_0, abs_0, zero_rpow, expectation_zero] \\
     Know ‘expectation p (λx. Normal (f (Y x))) ≠ PosInf ∧
           expectation p (λx. Normal (f (Y x))) ≠ NegInf’
     >- (irule expectation_finite \\
         fs [bounded_def] \\
         irule integrable_bounded \\
         fs [prob_space_def, random_variable_def] \\
         ONCE_REWRITE_TAC [CONJ_SYM] \\
         CONJ_TAC
         >- (qexists ‘λx. Normal a’ \\
             ONCE_REWRITE_TAC [CONJ_SYM] \\
             CONJ_TAC
             >- (irule integrable_const \\
                 fs [extreal_1_simps]) \\
             BETA_TAC \\
             GEN_TAC \\
             STRIP_TAC \\
             ‘abs (Normal (f (Y x))) = Normal (abs (f (Y x)))’ by METIS_TAC [extreal_abs_def] \\
             POP_ORW \\
             simp [extreal_11] \\
             Q.PAT_X_ASSUM ‘∀x. (∃x'. x = f x') ⇒ abs x ≤ a’
              (MP_TAC o (Q.SPEC ‘f ((Y :α -> real) x)’)) \\
             impl_tac
             >- (qexists ‘Y x’ \\
                 rw []) \\
                 simp []

             cheat) \\

         (* (λx. Normal (f (Y x))) ∈ Borel_measurable (measurable_space p) *)
         (MP_TAC o (Q.SPECL [‘measurable_space p’, ‘λx. f ((Y :α -> real) x)’]) o
                   (INST_TYPE [beta |-> ``:real``])) (IN_MEASURABLE_BOREL_IMP_BOREL') \\
         simp [] \\
         Know ‘(f o Y) ∈ borel_measurable (measurable_space p)’
         >- (MATCH_MP_TAC MEASURABLE_COMP \\
             Q.EXISTS_TAC ‘borel’ \\
             ‘f IN borel_measurable borel’ by PROVE_TAC [in_borel_measurable_continuous_on] \\
             fs [ p_space_def, events_def]) \\
         DISCH_TAC \\
         ‘Normal o f o Y ∈ Borel_measurable (measurable_space p)’
         by METIS_TAC [IN_MEASURABLE_BOREL_IMP_BOREL] \\
         fs [o_DEF]) \\
     rw [sub_refl])
 >> FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
 >> MP_TAC (Q.SPECL [‘diff’, ‘f’, ‘Y x’, ‘abs (X x)’] TAYLOR_CLT_LEMMA)
 >> simp []
 >> STRIP_TAC
 >> Q.ABBREV_TAC ‘M = sup {abs (Normal (diff 3 x)) | x | T}’
 >> FULL_SIMP_TAC std_ss []

 >> Know ‘expectation p (λx. Normal (diff 1 (Y x))) *
          expectation p (Normal ∘ (λx. X x)) =
          expectation p (λx. Normal (diff 1 (Y x)) * (Normal (X x)))’
 >- ((MP_TAC o (Q.SPECL [‘p’, ‘λx. Normal ((diff :num -> real -> real) 1 (Y x))’,
                              ‘Normal ∘ (λx. X x)’]) o
               (INST_TYPE [beta |-> ``:real``])) (GSYM indep_vars_expectation) \\
      simp [] \\
      Know ‘real_random_variable (λx. Normal (diff 1 (Y x))) p’
      >- (cheat) \\
      DISCH_TAC \\
      ‘real_random_variable (Normal ∘ (λx. X x)) p’ by METIS_TAC [o_DEF, real_to_extreal_rv] \\
      Know ‘indep_vars p (λx. Normal (diff 1 (Y x)))
                         (Normal ∘ (λx. X x)) Borel Borel’
      >- (cheat) \\
      DISCH_TAC \\
      Know ‘integrable p (λx. Normal (diff 1 (Y x)))’
      >- (cheat) \\
      DISCH_TAC \\
      ‘integrable p (Normal ∘ (λx. X x))’ by fs [o_DEF] \\
      rw [])
 >> DISCH_TAC
 >> POP_ORW
 >> Know ‘1 / 2 * expectation p (λx. Normal (diff 2 (Y x))) *
          expectation p (Normal ∘ (λx. (X x)²)) =
          expectation p (λx. Normal (1 / 2) * Normal (diff 2 (Y x)) * Normal ((X x)²))’
  >- (‘Normal (1 / 2 :real) = (1 / 2 :extreal)’ by cheat \\
      POP_ASSUM (rw o wrap o SYM) \\
      Know ‘Normal (1 / 2) * expectation p (λx. Normal (diff 2 (Y x))) =
            expectation p (λx. Normal (1 / 2) * Normal (diff 2 (Y x)))’
      >- (MP_TAC (Q.SPECL [‘p’, ‘λx. Normal ((diff :num -> real -> real) 2 (Y x))’, ‘1 / 2’]
                 (GSYM expectation_cmul)) \\
          simp [] \\
          Know ‘integrable p (λx. Normal (diff 2 (Y x)))’
          >- (cheat) \\
          simp []) \\
      DISCH_TAC \\
      POP_ORW \\
     (MP_TAC o (Q.SPECL [‘p’, ‘λx. Normal (1 / 2) * Normal ((diff :num -> real -> real) 2 (Y x))’,
                              ‘Normal ∘ (λx. (X x)²)’]) o
               (INST_TYPE [beta |-> ``:real``])) (GSYM indep_vars_expectation) \\
      simp [] \\
      cheat)
 >> DISCH_TAC
 >> POP_ORW
 >> cheat
QED
*)

(*
 >> ‘expectation p (λx. Normal (diff 1 (Y x))) *
     expectation p (λx. Normal (f (X x))) =
     expectation p (λx. Normal (diff 1 (Y x)) * Normal (f (X x)))’ by cheat
 >> POP_ORW
 >> ‘1 / 2 * expectation p (λx. Normal (diff 2 (Y x))) *
     expectation p (λx. Normal (f (X x powr 2))) =
     expectation p (λx. 1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2)))’ by cheat
 >> POP_ORW
 >> ‘expectation p (λx. Normal (f (Y x))) +
     expectation p (λx. Normal (diff 1 (Y x)) * Normal (f (X x))) =
     expectation p (λx. Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x)))’ by cheat
 >> POP_ORW
 >> ‘expectation p
     (λx. Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x))) +
     expectation p
     (λx. 1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2))) =
     expectation p
     (λx. Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x)) +
          1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2)))’ by cheat
 >> POP_ORW
 >> ‘expectation p (λx. Normal (f (Y x + X x))) −
     expectation p
     (λx. Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x)) +
          1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2))) =
     expectation p
     (λx. Normal (f (Y x + X x)) −
          (Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x)) +
                      1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2))))’ by cheat
 >> POP_ORW
 >> ‘M ≠ NegInf’ by simp [taylor_thm]
 >> Cases_on ‘X x = 0’
 >- (cheat)

    >> Cases_on ‘M = PosInf’
    >- (cheat)
    >> ‘∃r. M = Normal r’ by METIS_TAC [extreal_cases]
    >> simp [o_DEF]
    >> ‘6 = Normal 6’ by rw [extreal_of_num_def]
    >> POP_ORW
    >> ‘Normal r / Normal 6 = Normal (r / 6)’ by rw [extreal_div_eq]
    >> POP_ORW
    >> Know ‘integrable p (λx'. abs (Normal (X x' pow 3)))’
    >- (MP_TAC (Q.SPECL [‘p’, ‘λx. Normal (X x pow 3)’]
                 integrable_abs) \\
        FULL_SIMP_TAC std_ss [prob_space_def, o_DEF])
    >> DISCH_TAC
    >> ‘Normal (r / 6) * expectation p (λx. abs (Normal (X x)³)) =
        expectation p (λx. Normal (r / 6) * abs (Normal (X x)³))’ by METIS_TAC [expectation_cmul]
    >> POP_ORW
    >> Q.ABBREV_TAC ‘Z = λx.
                            Normal (f (Y x + X x)) −
                                   (Normal (f (Y x)) +
                                    Normal (diff 1 (Y x)) * Normal (f (X x)) +
                                    1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2)))’
    >> ‘abs (expectation p Z) ≤ expectation p (abs o Z)’ by cheat
    >> Know ‘expectation p (abs ∘ Z) ≤ expectation p (λx. Normal (r / 6) * abs (Normal (X x)³))’
    >- (irule expectation_mono_alt
  >> simp []
  >> CONJ_TAC
  (* ∀x. x ∈ p_space p ⇒
            Normal (f (Y x + X x)) −
            (Normal (f (Y x)) + Normal (diff 1 (Y x)) * Normal (f (X x)) +
             1 / 2 * Normal (diff 2 (Y x)) * Normal (f (X x powr 2))) ≤
            Normal (r / 6) * abs (Normal (X x)³) *)
  >- (GEN_TAC \\
      rw [] \\
      cheat)
  >> CONJ_TAC
  >- (cheat)
  >> cheat \\
    cheat)
    >> DISCH_TAC
    >> METIS_TAC [le_trans]
QED
*)
(* ------------------------------------------------------------------------- *)
(*  Normal density                                                           *)
(* ------------------------------------------------------------------------- *)

Definition absolute_third_moment_def:
  absolute_third_moment p X  = absolute_moment p X 0 3
End

Definition second_moments_def:
  second_moments p X n = SIGMA (λi. central_moment p (X i) 2) (count1 n)
End

Definition third_moments_def:
  third_moments p X n = SIGMA (λi. third_moment p (X i)) (count1 n)
End

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

Theorem normal_absolute_third_moment:
  ∀p X sig. normal_rv X p 0 sig ⇒
            absolute_third_moment p X = sqrt (8 / π)  *  variance p X  * sqrt (variance p X)
Proof
  cheat
QED

Theorem clt_tactic1:
  ∀p X Y N s b. prob_space p ∧
                (∀i. real_random_variable (X i) p) ∧
                (∀i j. indep_vars p (X i) (X j) Borel Borel) ∧
                (∀i. expectation p (X i) = 0) ∧
                (∀i. central_moment p (X i) 2 < PosInf) ∧
                (∀i. integrable p (X i)) ∧
                (∀n. s n = sqrt (second_moments p X n)) ∧
                (∀n. s n ≠ 0) ⇒
                ∀i. real_random_variable (((λn x. ∑ (λi. X i x) (count1 n) / s n)) i) p
Proof
  rpt STRIP_TAC
  >> BETA_TAC
  >> ‘sqrt (second_moments p X i) = s i’ by fs []
  >> Know ‘∀n. 0 ≤ s n’
  >- (fs [] \\
         GEN_TAC \\
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
  >> ‘∀n. 0 < s n’ by rw[lt_le]
  >> ‘∀n. inv(s n) ≠ NegInf ∧ inv(s n) ≠ PosInf’ by METIS_TAC[inv_not_infty]
  >> ‘∃r. Normal r = inv(s i)’ by METIS_TAC[extreal_cases]
  >> Q.ABBREV_TAC ‘D = λx. ∑ (λi. X i x) (count1 i)’
  >> ‘∀x. D x = ∑ (λi. X i x) (count1 i)’ by rw[Abbr ‘D’]

  >> Know ‘∀x. D x ≠ NegInf’
  >- (rw[Abbr ‘D’] \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_NEGINF \\
      CONJ_TAC >- REWRITE_TAC [FINITE_COUNT] \\
      Q.X_GEN_TAC ‘x'’ \\
      FULL_SIMP_TAC std_ss [real_random_variable_def]\\
      Q.PAT_X_ASSUM ‘ ∀i'.
                           random_variable (X i') p Borel ∧
                           ∀x. x ∈ p_space p ⇒ X i' x ≠ −∞ ∧ X i' x ≠ +∞’
      (MP_TAC o Q.SPEC ‘x'’) \\
      STRIP_TAC \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘x’) \\
      STRIP_TAC \\

     cheat)
  >> DISCH_TAC
  >> Know ‘∀x. D x ≠ PosInf’
  >- (rw[Abbr ‘D’] \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
      cheat)
  >> DISCH_TAC

  >> ‘∀x. D x / s i = inv(s i) * D x’ by METIS_TAC[div_eq_mul_linv]
  >> ‘∀x. D x / s i = Normal r * D x’ by METIS_TAC[div_eq_mul_linv]
  >> Q.UNABBREV_TAC ‘D’
  >> ‘∀x. real_random_variable (λx. Normal r * ∑ (λi. X i x) (count1 i)) p’
      by rw [real_random_variable_cmul, real_random_variable_sum]
  >> Know ‘∀x. x IN p_space p ==>
               inv(s i) * ∑ (λi. X i x) (count1 i) = Normal r * ∑ (λi. X i x) (count1 i)’
  >- (X_GEN_TAC “x” \\
      DISCH_TAC \\
      METIS_TAC[])
  >> DISCH_TAC
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. inv(s i) * ∑ (λi. X i x) (count1 i)’,
                           ‘λx. Normal r * ∑ (λi. X i x) (count1 i)’]
              real_random_variable_cong)
  >> impl_tac
  >- (PROVE_TAC [])
  >> MP_TAC (Q.SPECL [‘p’, ‘λx. inv(s i) * ∑ (λi. X i x) (count1 i)’,
                      ‘λx. ∑ (λi. X i x) (count1 i) / s i’]
              real_random_variable_cong)
  >> impl_tac
  >- (METIS_TAC[])
  >> METIS_TAC []
QED

(*
Theorem converge_in_dist_third_alt':
    !p X Y. prob_space p /\
            (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
            ((X --> Y) (in_distribution p) <=>
            (∀(i :num). i IN {0; 1; 2; 3} ⇒ bounded (IMAGE (diff i) 𝕌(:real))) ∧
            (∀(i :num). i IN {0; 1; 2; 3} ⇒ (diff i) continuous_on 𝕌(:real)) ⇒
            ((\n. expectation p (Normal o f o real o (X n))) -->
                  expectation p (Normal o f o real o Y)) sequentially)
Proof
    cheat
QED
*)

Theorem lim_null:
    ∀f l.
          (∃N. ∀n. N ≤ n ⇒ f n ≠ +∞ ∧ f n ≠ −∞) ∧ l ≠ +∞ ∧ l ≠ −∞ ⇒
          (f --> l) sequentially ⇔ ((λn. (real (f n) − real l)) --> 0) sequentially
Proof
    rw [EQ_IMP_THM]
 >- ((MP_TAC o (Q.SPECL [‘sequentially’, ‘real o f’, ‘real l’]) o
     (INST_TYPE [alpha |-> ``:num``])) real_topologyTheory.LIM_NULL \\
     rw [o_DEF] \\
     Suff ‘((λx. real (f x)) ⟶ real l) sequentially’
     >- (fs []) \\
     cheat)

 >> (MP_TAC o (Q.SPECL [‘sequentially’, ‘real o f’, ‘real l’]) o
              (INST_TYPE [alpha |-> ``:num``])) real_topologyTheory.LIM_NULL
 >> rw [o_DEF]

 >> ‘∃a. l = Normal a’ by METIS_TAC [extreal_cases]
 >> cheat
QED

(*
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
               (∀i. integrable p (X i)) ∧
               (∀n. s n = sqrt (second_moments p X n)) ∧
               (∀n. s n ≠ 0) ∧
               (∀n. b n = third_moments p X n) ∧
               ((\n. b n / (s n pow 3)) --> 0) sequentially ⇒
               ((\n x. (SIGMA (λi. X i x) (count1 n)) / s n) --> N) (in_distribution p)
Proof
     rpt STRIP_TAC
  >> Q.ABBREV_TAC ‘R = λn x. ∑ (λi. X i x) (count1 n) / s n’
  >> Know ‘∀i. real_random_variable (R i) p’
  >- (rw [Abbr ‘R’] \\
      METIS_TAC [clt_tactic1])
  >> DISCH_TAC
  >> fs [normal_rv_def, converge_in_dist_alt']
  >> rpt STRIP_TAC

     >> Q.ABBREV_TAC ‘M = λn. expectation p (Normal ∘ f ∘ real ∘ R n)’
     >> Q.ABBREV_TAC ‘Q = expectation p (Normal ∘ f ∘ real ∘ N)’
     (* real_topologyTheory.LIM_NULL *)
     >> Suff ‘((λx. M x - Q) --> 0) sequentially’
     >- (cheat)
     >> rw [Abbr ‘M’, Abbr ‘Q’]
     >> Know ‘∀x. expectation p (Normal ∘ f ∘ real ∘ Y x) =
                  expectation p (Normal ∘ f ∘ real ∘ N)’
     >- (cheat)
     >> DISCH_TAC
     >> ‘(λx.
              expectation p (Normal ∘ f ∘ real ∘ R x) −
              expectation p (Normal ∘ f ∘ real ∘ N)) =
         (λx.
              expectation p (Normal ∘ f ∘ real ∘ R x) −
              expectation p (Normal ∘ f ∘ real ∘ Y x))’
        by METIS_TAC []
     >> DISCH_TAC
     >> qmatch_abbrev_tac ‘(g --> 0) sequentially’
                              >> Q.PAT_X_ASSUM ‘g = _’ (ONCE_REWRITE_TAC o wrap)
          >> simp []
     >> POP_ASSUM (rw o wrap o SYM)

(*

     >> ‘expectation p (Normal ∘ f ∘ real ∘ N) ≠ NegInf ∧
         expectation p (Normal ∘ f ∘ real ∘ N) ≠ PosInf’ by cheat
     >> ‘∃a. expectation p (Normal ∘ f ∘ real ∘ N) = Normal a’ by METIS_TAC [extreal_cases]
     >> rw []

     >> ‘∀n. expectation p (Normal ∘ f ∘ real ∘ R n) ≠ NegInf ∧
             expectation p (Normal ∘ f ∘ real ∘ R n) ≠ PosInf’ by cheat
     >> Know ‘∃c. (λn. expectation p (Normal ∘ f ∘ real ∘ R n)) = Normal o c’
     >- (cheat)
     >> DISCH_TAC
     >> rw []
            >> rw []
     >> irule lim_sequentially_imp_extreal_lim
     >> irule extreal_lim_sequentially_eq *)

     >> cheat
QED
*)

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
    ∀p X r s. prob_space p ∧ real_random_variable X p ⇒
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
