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
     probabilityTheory derivativeTheory integralTheory extreal_baseTheory;

val _ = new_theory "central_limit";



Definition normal_density :
    normal_density mu sig x =
      (1 / sqrt (2 * pi * sig pow 2)) * exp (-((x - mu) pow 2) / (2 * sig pow 2))
End

Overload std_normal_density = “normal_density 0 1”

Theorem std_normal_density_def :
    !x. std_normal_density x = (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
Proof
    RW_TAC std_ss [normal_density]
 >> SIMP_TAC real_ss [REAL_SUB_RZERO, POW_ONE]
QED

Theorem normal_density_nonneg :
    !mu sig x. 0 <= normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]
QED

Theorem normal_density_pos :
    !mu sig. 0 < sig ==> 0 < normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT >> art []
QED

Theorem normal_density_continuous_on :
    !mu sig s. normal_density mu sig continuous_on s
Proof
    rpt GEN_TAC
 >> ‘normal_density mu sig =
       (\x. 1 / sqrt (2 * pi * sig pow 2) *
            exp (-((x - mu) pow 2) / (2 * sig pow 2)))’
       by rw [normal_density, FUN_EQ_THM]
 >> POP_ORW
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- (‘$* (1 / sqrt (2 * pi * sig pow 2)) = \x. (1 / sqrt (2 * pi * sig pow 2)) * x’
       by rw [FUN_EQ_THM] >> POP_ORW \\
     HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL >> rw [CONTINUOUS_ON_ID])
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- rw [CONTINUOUS_ON_EXP]
 >> REWRITE_TAC [real_div, Once REAL_MUL_COMM]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> REWRITE_TAC [Once REAL_NEG_MINUS1]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_POW
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_SUB
 >> rw [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]
QED

Theorem in_measurable_borel_normal_density :
    !mu sig. normal_density mu sig IN borel_measurable borel
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC in_borel_measurable_continuous_on
 >> rw [normal_density_continuous_on]
QED

Theorem IN_MEASURABLE_BOREL_normal_density :
    !mu sig. Normal o normal_density mu sig IN Borel_measurable borel
Proof
    rpt GEN_TAC
 >> HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL'
 >> rw [sigma_algebra_borel, in_measurable_borel_normal_density]
QED


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

(* ------------------------------------------------------------------------- *)

Definition third_moment_def:
  third_moment p X = central_moment p X 3
End

Definition absolute_third_moment_def:
  absolute_third_moment p X  = absolute_moment p X 0 3
End

Theorem converge_in_dist_cong_full:
  !p X Y A B m. prob_space p ∧
                (!n x. m <= n /\ x IN p_space p ==> X n x = Y n x) /\
                (!x. x IN p_space p ==> A x = B x) ==>
                ((X --> A) (in_distribution p) <=> (Y --> B) (in_distribution p))
Proof
  rw [converge_in_dist, EXTREAL_LIM_SEQUENTIALLY]
  >> EQ_TAC >> rw []
  (*  ∃N. ∀n. N ≤ n ⇒
         dist extreal_mr1 (expectation p (f ∘ Y n),expectation p (f ∘ B)) < e *)
  >> Q.PAT_X_ASSUM ‘ ∀f. f bounded_on 𝕌(:extreal) ∧ f ∘ Normal continuous_on 𝕌(:real)
                         ==> P’ (MP_TAC o (Q.SPEC ‘f’)) >> rw []
  >> POP_ASSUM (MP_TAC o (Q.SPEC ‘e’)) >> rw []
  >> Q.EXISTS_TAC ‘MAX N m’ >> rw [MAX_LE]
  >- (Know ‘expectation p (f ∘ Y n) =
           expectation p (f ∘ X n)’
  >- (MATCH_MP_TAC expectation_cong \\ rw[])
  >> DISCH_TAC
  >> Know ‘expectation p (f ∘ B) =
           expectation p (f ∘ A)’
  >- (MATCH_MP_TAC expectation_cong \\ rw[])
  >> DISCH_TAC
  >> METIS_TAC [])
  >> Know ‘expectation p (f ∘ Y n) =
           expectation p (f ∘ X n)’
  >- (MATCH_MP_TAC expectation_cong \\ rw[])
  >> DISCH_TAC
  >> Know ‘expectation p (f ∘ B) =
           expectation p (f ∘ A)’
  >- (MATCH_MP_TAC expectation_cong \\ rw[])
  >> DISCH_TAC
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

Theorem liapounov_ineq_lemma:
  !m u p.
    measure_space m ∧
    measure m (m_space m) < PosInf ∧
    1 < p ∧ p < PosInf ∧
    u ∈ lp_space p m  ⇒
      ∫⁺ m (λx. abs (u x)) ≤ seminorm p m u * ((measure m (m_space m)) powr (1 - inv(p)))
Proof
  rpt STRIP_TAC
  >> ‘p ≠ PosInf’ by rw[lt_imp_ne]
  >> ‘0 < p’ by METIS_TAC [lt_trans, lt_01]
  >> ‘p ≠ 0’ by rw[lt_imp_ne]
  >> ‘inv(p) ≠ NegInf ∧  inv(p) ≠ PosInf’ by rw[inv_not_infty]
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
        >- (‘1 = Normal 1’ by rw[] \\
            rw[]) \\
      rw[])
  >> DISCH_TAC
  >> Know ‘1 - inv(p) ≠ PosInf’
  >- (‘∃b. inv(p) = Normal b’ by METIS_TAC [extreal_cases]
      >> ‘∃d. Normal 1 - Normal b = Normal d’ by METIS_TAC [extreal_sub_def]
      >> Know ‘1 - inv(p) = Normal d’
      >- (‘1 = Normal 1’ by rw[]
          >> rw[])
      >> rw[])
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
          MP_TAC ( Q.SPECL [‘p’, ‘1’]
                    inv_lt_antimono) \\
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
      >- ( MP_TAC (Q.SPECL [‘m’, ‘1’] pos_fn_integral_const) \\
           impl_tac \\
           simp[] \\
           ‘1 * measure m (m_space m) =  measure m (m_space m) ’ by rw[mul_lone] \\
           simp[] \\
           DISCH_TAC \\
           METIS_TAC[]
         ) \\
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
      >> cheat)
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


Theorem taylor_series:
  ∀x y M f f' net. (f has_derivative f') net ⇒
                    abs (f (x + y) - [ f (x) + f'(x) * y ]) ≤ M * abs (y) powr 3 / 6
Proof
  cheat
QED


Definition gamma_function_def:
  gamma_function f z ⇔ z
End

Theorem moment_pdf_def:
  ∀p X Y a r. moment (density p X) Y a r =
              expectation p (λx. (Y x - a) powr &r * normal_density mu sig x)
Proof
  rpt STRIP_TAC
  >> rw [moment_def]
  >> cheat

QED



Theorem normal_absolute_third_moment:
  ∀p X sig. normal_rv X p 0 sig ⇒
            absolute_third_moment p X = sqrt (8/π)  *  variance p X  * sqrt (variance p X)
Proof
  rpt STRIP_TAC
  >> rw[absolute_third_moment_def, absolute_moment_def, normal_rv_def]
  >> FULL_SIMP_TAC std_ss [normal_rv_def, normal_measure_def]

  >>  ‘normal_density 0 sig x =
       (1 / sqrt (2 * pi * sig pow 2) *
        exp (-(x pow 2) / (2 * sig pow 2)))’
    by rw [normal_density, FUN_EQ_THM]
  >> cheat
QED


Definition second_moments_def:
  second_moments p X n = SIGMA (λi. central_moment p (X i) 2) (count1 n)
End


Definition third_moments_def:
  third_moments p X n = SIGMA (λi. third_moment p (X i)) (count1 n)
End


Theorem central_limit:
  ∀p X N s b. prob_space p ∧
              (∀i. real_random_variable (X i) p) ∧
              normal_rv N p 0 (real (standard_deviation p (X 0))) ∧
              (∀i. expectation p (X i) = 0) ∧
              (∀i. central_moment p (X i) 2 < PosInf) ∧
              (∀i. third_moment p (X i) < PosInf) ∧
              (∀n. s n = sqrt (second_moments p X n)) ∧
              (∀n. b n = third_moments p X n) ∧
              ((\n. b n / (s n pow 3)) --> 0) sequentially
            ⇒ ((\n x. (Σ (λi. X i x) (count1 n)) / s n) --> N) (in_distribution p)
Proof
  rpt STRIP_TAC
  >> rw [converge_in_dist]
  >> cheat

QED





(* ------------------------------------------------------------------------- *)






(*
Definition mgf_def:
  mgf p X s  =
  expectation p (\x. exp (Normal s * X x))
End
*)

(*
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
  >- ( MATCH_MP_TAC expectation_cong  >> rw[] >> AP_TERM_TAC
      >> ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases] >> rw[]
      >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[add_ldistrib_normal2]
    ) >> Rewr'
  >> Know ‘expectation p
           (λx. exp (Normal s * (Normal a * X x) + Normal s * Normal b)) =
           expectation p (λx. (exp (Normal s * (Normal a * X x))) * exp (Normal s * Normal b))’
  >- ( MATCH_MP_TAC expectation_cong
       >> rw[exp_add]
       >>  ‘∃c. X x = Normal c’ by METIS_TAC [extreal_cases]>> rw[]
       >> ‘∃d. Normal a * Normal c = Normal d’ by METIS_TAC [extreal_mul_eq] >> rw[]
       >> ‘∃e. Normal s * Normal d = Normal e’ by METIS_TAC [extreal_mul_eq] >> rw[]
       >> ‘∃f. Normal s * Normal b = Normal f’ by METIS_TAC [extreal_mul_eq] >> rw[exp_add]
     ) >> Rewr'
  >> ‘∃g. exp (Normal s * Normal b) = Normal g’ by  METIS_TAC [extreal_mul_eq, normal_exp]
  >> rw[]
  >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [mul_comm]
  >> rw [mul_assoc, extreal_mul_eq]
  >> HO_MATCH_MP_TAC expectation_cmul
  >> ASM_REWRITE_TAC []
QED

Theorem mgf_sum:
  !p X Y s . prob_space p /\ real_random_variable X p  /\
             real_random_variable Y p  /\ indep_vars p X Y Borel Borel
             ∧  mgf p (\x. X x + Y x) s ≠ PosInf ∧  mgf p X s ≠ PosInf
             ∧  mgf p Y s ≠ PosInf  ==>
            mgf p (\x. X x + Y x) s = mgf p X s * mgf p Y s
Proof
  rw [mgf_def, real_random_variable_def]
  >> Know ‘expectation p (\x. exp (Normal s * (X x + Y x))) =
                       expectation p (\x. exp ((Normal s * X x) + (Normal s * Y x)))’
  >-( MATCH_MP_TAC expectation_cong >> rw[] >> AP_TERM_TAC
      >> MATCH_MP_TAC add_ldistrib_normal >> rw[])
      >> Rewr'
  >> Know ‘ expectation p (λx. exp (Normal s * X x + Normal s * Y x)) =
            expectation p (λx. exp (Normal s * X x) * exp (Normal s * Y x))’
  >- ( MATCH_MP_TAC expectation_cong  >> rw[] >> MATCH_MP_TAC exp_add >> DISJ2_TAC
       >> ‘∃a. X x = Normal a’ by METIS_TAC [extreal_cases]
       >>  ‘∃b. Y x = Normal b’ by METIS_TAC [extreal_cases]
       >> rw[extreal_mul_eq]) >> Rewr'
  >> HO_MATCH_MP_TAC indep_vars_expectation
  >> simp[]

  >> CONJ_TAC
     (* real_random_variable (λx. exp (Normal s * X x)) p *)
  >- ( MATCH_MP_TAC real_random_variable_exp_normal
       >>  fs[real_random_variable, random_variable_def] )

  >> CONJ_TAC
     (* real_random_variable (λx. exp (Normal s * X x)) p *)
  >- ( MATCH_MP_TAC real_random_variable_exp_normal
       >>  fs[real_random_variable, random_variable_def] )

  >> CONJ_TAC
     (* indep_vars p (λx. exp (Normal s * X x)) (λx. exp (Normal s * Y x)) Borel Borel *)
  >- ( Q.ABBREV_TAC ‘f = λx. exp (Normal s * x)’
       >> simp []
       >> MATCH_MP_TAC ( REWRITE_RULE [o_DEF] indep_rv_cong )   >> csimp[]
       >> Q.UNABBREV_TAC ‘f’
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> simp [] >> Q.EXISTS_TAC ‘λx. Normal s * x’ >> simp[SIGMA_ALGEBRA_BOREL]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘λx. x’, ‘s’]
       >> simp[SIGMA_ALGEBRA_BOREL,  IN_MEASURABLE_BOREL_BOREL_I])

  >> Know ‘(λx. exp (Normal s * X x)) ∈ Borel_measurable (measurable_space p)’
  >- ( MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> Q.EXISTS_TAC ‘λx. Normal s * X x’
       >> fs [prob_space_def, measure_space_def]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘X’, ‘s’] >> simp[random_variable_def]
       >> fs [random_variable_def, p_space_def, events_def])
  >> DISCH_TAC

  >> Know ‘(λx. exp (Normal s * Y x)) ∈ Borel_measurable (measurable_space p)’
  >- ( MATCH_MP_TAC IN_MEASURABLE_BOREL_EXP
       >> Q.EXISTS_TAC ‘λx. Normal s * Y x’
       >> fs [prob_space_def, measure_space_def]
       >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
       >> qexistsl [‘Y’, ‘s’] >> simp[random_variable_def]
       >> fs [random_variable_def, p_space_def, events_def])
  >> DISCH_TAC

  >> Q.ABBREV_TAC ‘f = λx. exp (Normal s * X x)’ >> simp []
  >> ‘∀x. x ∈ p_space p ⇒ 0 ≤  f x’ by METIS_TAC [exp_pos]
  >> Q.ABBREV_TAC ‘g = λx. exp (Normal s * Y x)’ >> simp []
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

(*------------------------------------------------------------------*)

Theorem mgf_sum_independent:
  ∀p X s (J : 'index set). prob_space p /\ FINITE J /\
                           (∀i. i IN J ⇒ real_random_variable (X i) p)
                           ==> mgf p (λx. SIGMA (λi. X i x) J) s =
                                   PI (λi. mgf p (X i) s) J
Proof
  rpt GEN_TAC
  >> STRIP_TAC
  >> FULL_SIMP_TAC std_ss [mgf_def]
  >> Know ‘expectation p (λx. exp (Normal s * ∑ (λi. X i x) J)) =
           expectation p (λx.  ∏ (λi. exp (Normal s * X i x)) J)’
           >- ( MATCH_MP_TAC expectation_cong >> rw[]

)



QED



Theorem mgf_uniqueness_discreate:
  ∀p X Y s. prob_space p ∧ FINITE (p_space p) ∧
                       real_random_variable X p ∧
                       real_random_variable Y p ∧
            mgf p X s ≠ PosInf ∧
            mgf p X s ≠ NegInf ∧
            mgf p Y s ≠ PosInf ∧
            mgf p Y s ≠ NegInf ∧
            mgf p X s = mgf p Y s ⇒
            distribution p X = distribution p Y
Proof


QED


Theorem mgf_uniqueness:
  ∀p X Y s. prob_space p ∧ real_random_variable X p ∧ real_random_variable Y p ∧
            mgf p X s ≠ PosInf ∧
            mgf p X s ≠ NegInf ∧
            mgf p Y s ≠ PosInf ∧
            mgf p Y s ≠ NegInf ∧
            mgf p X s = mgf p Y s ⇒
            distribution p X =  distribution p Y
Proof
  rw [mgf_def, distribution_def]

  >> qexists_tac ‘x’

  (** expectation p (λx. exp (Normal s * X x)) =
           expectation p (λx. exp (Normal s * Y x)) **)
  >> Q.PAT_X_ASSUM ‘expectation p (λx. exp (Normal s * X x)) =
                    expectation p (λx. exp (Normal s * Y x))’ MP_TAC
  >> MATCH_MP_TAC expectation_cong
QED



(*independent_identical_distribution*)
Definition iid_def:
  iid p X E A J ⇔  identical_distribution p X E J ∧
                 pairwise_indep_vars p X A J
End

Definition normal_distribution_def:
  ∀ p X J. normal_distribution p X J M V ⇔
           real_random_variable p X ∧
           (∀ i. i ∈ J) ∧
           M = expectation p (λi. X i) ∧ M  ≠ PosInf ∧ M ≠ NegInf ∧
           V = variance p X ∧ V > 0 ∧ V ≠ PosInf ⇒
           pdf p X =
           (1 / (sqrt (2 * pi * V))) *
           exp ( - ((X i - M) ** 2) / (2 * V))
End

Theorem central_limit_theorem_iid:
  ∀p X E A J . prob_space p ∧
               iid p X E A J ∧
               (∀i. i IN J ⇒ variance p (X i) ≠ PosInf ∧
               variance p (X i) ≠ NegInf) ∧
               (∀i. i IN J ⇒ real_random_variable (X i) p) ⇒
               ( (λi x. (Σ (X i x) J / n) - expectation p (X i)) /(sqrt (variance p (X 0)) / sqrt(& i)) -->
                    normal_distribution p X J 0 1  (in_distribution p)
Proof
QED


Theorem mgf_derivative:
  ∀mgf mgf' p X s. (mgf p X s) has_derivative (mgf' p X s) net (at 0) ⇒
            mgf' p X 0 = expectation p (\x.  X x)
Proof
QED



*)

(*---------------------------------------------------------------------------*
 * Write the theory to disk.                                                 *
 *---------------------------------------------------------------------------*)

val _ = export_theory();
val _ = html_theory "central_limit";

(* References:

  [1] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).
  [2] Shiryaev, A.N.: Probability-2. Springer-Verlag New York (2019).
  [3] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).

 *)
