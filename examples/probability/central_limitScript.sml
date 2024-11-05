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


Theorem seminorm_one:
  !p m. measure_space m /\ 1 < p ==> seminorm p m (\x. 1) = 1
Proof
  rpt STRIP_TAC
  >> Know ‘(\x. 1) IN measurable (measurable_space m) Borel’
  >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
      Q.EXISTS_TAC ‘1’ >> fs [measure_space_def])
  >> DISCH_TAC
  >> Cases_on ‘p = PosInf’
  >- (rw [seminorm_infty_alt, inf_eq'] >| (* 2 subgoals *)
      [ (* goal 1 (of 2) *)
        MATCH_MP_TAC lt_imp_le >> art [],
        (* goal 2 (of 2) *)
        MATCH_MP_TAC le_epsilon >> rw [] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> rw [AE_T] ])
  >> ‘0 < inv p’ by PROVE_TAC [inv_pos']
  >> rw [seminorm_normal, zero_rpow, pos_fn_integral_zero]
QED

Theorem liapounov_ineq:
  !m u v p.
      measure_space m ∧ 1 < p ∧ p < PosInf ∧
      u ∈ lp_space p m  ⇒
      ∫⁺ m (λx. abs (u x)) ≤ seminorm p m u
Proof

  rpt STRIP_TAC
  >> ‘p ≠ PosInf’ by rw[lt_imp_ne]
  >> ‘0 < p’ by METIS_TAC [lt_trans, lt_01]
  >> ‘p ≠ 0’ by rw[lt_imp_ne]
  >> ‘0 < inv (p)’ by METIS_TAC [inv_pos']
  >> ‘inv(p) ≠ 0’ by rw[lt_imp_ne]
  >> Know ‘inv (p) < 1’
  >- (cheat)
  >> DISCH_TAC
  >> ‘0 < 1 - inv(p)’ by rw[sub_zero_lt]
  >> ‘1 - inv(p) ≠ 0’ by rw[lt_imp_ne]
  >> ‘inv(p) ≠ NegInf ∧  inv(p) ≠ PosInf’ by rw[inv_not_infty]
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
  >> MP_TAC (Q.SPECL [‘m’, ‘u’, ‘λx. 1’, ‘p’, ‘q’]
              Hoelder_inequality')
  >> impl_tac
  >> simp[]
  >> sg ‘0 < q’ (* 0 < q *)
  >- (Q.UNABBREV_TAC ‘q’ \\
      MATCH_MP_TAC inv_pos' \\
      CONJ_TAC (*  0 < 1 − p⁻¹ *)
      >- (MATCH_MP_TAC sub_zero_lt \\
          MP_TAC ( Q.SPECL [‘p’, ‘1’]
                    inv_lt_antimono) \\
          simp[lt_01, inv_one])
      (*  1 − p⁻¹ ≠ +∞ *)
      >> rw[])
  >> CONJ_TAC
  >- (rw[])

  (* (λx. 1) ∈ lp_space q m*)
   >- (Know ‘q ≠ PosInf’
       >- (Q.UNABBREV_TAC ‘q’ \\
           rw[inv_not_infty])
       >> DISCH_TAC
       >> rw[lp_space_def]
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
       >> Know ‘ ∫⁺ m (λx. Normal 1) = Normal 1 * measure m (m_space m)’
       >- (MATCH_MP_TAC pos_fn_integral_const \\
           sg ‘measure m (m_space m) < +∞’ \\
           ‘measure m (m_space m) ≠ +∞’ by  rw[lt_imp_ne]
           cheat
       >> DISCH_TAC >> cheat
       >> DISCH_TAC
       >> Know ‘seminorm q m (λx. 1) = 1’
       >- (rw[seminorm_def]
          cheat)
       >> DISCH_TAC
       >> METIS_TAC [])
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
