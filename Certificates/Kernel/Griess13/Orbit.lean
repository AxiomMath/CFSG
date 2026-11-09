module

public import CFSG.Monster.GMS.Griess13.ChecksOrbitTab

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelG13

open CFSG.Monster.GMS.Griess13.Co1Data
open scoped Matrix

theorem digit6 (d : Fin 6 → ℕ) (hd : ∀ k, d k < 3) (i : Fin 6) :
    (∑ k : Fin 6, 3 ^ k.val * d k) / 3 ^ i.val % 3 = d i := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  have h4 := hd 4
  have h5 := hd 5
  simp only [Fin.sum_univ_six]
  fin_cases i <;> simp <;> omega

theorem codeOf_as (v : Fin 6 → ZMod 3) : codeOf v = ∑ k : Fin 6, 3 ^ k.val * (v k).val := by
  unfold codeOf
  exact Finset.sum_congr rfl fun k _ => Nat.mul_comm _ _

theorem codeOf_lt : ∀ v : Fin 6 → ZMod 3, codeOf v < 729 := by
  intro v
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  rw [codeOf_as]
  simp only [Fin.sum_univ_six]
  simp
  omega

theorem vecOfCode_codeOf : ∀ v : Fin 6 → ZMod 3, vecOfCode (codeOf v) = v := by
  intro v
  funext i
  apply ZMod.val_injective
  simp only [vecOfCode, ZMod.val_natCast, Nat.mod_mod]
  rw [codeOf_as]
  exact digit6 (fun k => (v k).val) (fun k => ZMod.val_lt (v k)) i

theorem codeOf_vecOfCode : ∀ c < 729, codeOf (vecOfCode c) = c := by
  intro c hc
  rw [codeOf_as]
  simp only [vecOfCode, ZMod.val_natCast, Nat.mod_mod, Fin.sum_univ_six]
  simp
  omega

theorem vecOfCode_zero : vecOfCode 0 = 0 := by
  funext i
  simp [vecOfCode]

theorem codeOf_pos : ∀ v : Fin 6 → ZMod 3, v ≠ 0 → 0 < codeOf v := by
  intro v hv
  refine Nat.pos_of_ne_zero fun h => hv ?_
  rw [← vecOfCode_codeOf v, h, vecOfCode_zero]

theorem vecOfCode_ne_zero : ∀ c < 729, 0 < c → vecOfCode c ≠ 0 := by
  intro c hc hpos h
  have e := codeOf_vecOfCode c hc
  rw [h, ← vecOfCode_zero, codeOf_vecOfCode 0 (by omega)] at e
  omega

theorem forall_vec {P : (Fin 6 → ZMod 3) → Prop} (h : ∀ c < 729, P (vecOfCode c)) : ∀ v, P v :=
  fun v => vecOfCode_codeOf v ▸ h _ (codeOf_lt v)

theorem card_codeVec (P : (Fin 6 → ZMod 3) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ((Finset.range 729).filter fun c => P (vecOfCode c)).card := by
  symm
  refine Finset.card_bij (fun c _ => vecOfCode c) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc.2
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    rw [← codeOf_vecOfCode a ha.1, ← codeOf_vecOfCode b hb.1, hab]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨codeOf v, ?_, vecOfCode_codeOf v⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨codeOf_lt v, by rw [vecOfCode_codeOf]; exact hv⟩

theorem vecOfCode_ne_zero_iff {c : ℕ} (hc : c < 729) : vecOfCode c ≠ 0 ↔ c ≠ 0 := by
  constructor
  · rintro h rfl
    exact h vecOfCode_zero
  · intro h
    exact vecOfCode_ne_zero c hc (Nat.pos_of_ne_zero h)

theorem toArray_get! (L : List ℕ) (c : ℕ) : L.toArray[c]! = L.getD c 0 := by
  rw [List.getD_eq_getElem?_getD]
  simp only [getElem!_def, List.getElem?_toArray]
  cases L[c]? <;> rfl

theorem cls_get (c : ℕ) : orbTabR.1[c]! = CFSG.Monster.GMS.Griess13.OrbTab.cls.getD c 0 :=
  toArray_get! _ c

def g13PackW (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ w * g13PackW w xs

theorem g13PackW_getD (w : ℕ) : ∀ L : List ℕ, (∀ x ∈ L, x < 2 ^ w) → ∀ c,
    L.getD c 0 = g13PackW w L / 2 ^ (w * c) % 2 ^ w
  | [], _, c => by simp [g13PackW]
  | x :: xs, h, 0 => by
    rw [List.getD_cons_zero, g13PackW, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h x (by simp))]
  | x :: xs, h, c + 1 => by
    have hx : x < 2 ^ w := h x (by simp)
    rw [List.getD_cons_succ, g13PackW_getD w xs (fun y hy => h y (by simp [hy])) c, g13PackW,
      Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * c)), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]

def g13ClsP : ℕ := 7849836030598479775101022485376827873057649407007624259330474911327090041154881786509694084496389488803161301306561430034428451384102003917409173557039339854419401634315391586393303190680269504389942144277536065925114662977739352544943961873893036839493440372413914936934362455169585814869971596405232353854079475014817094785433293454339350562664105158497100115219391539099371775765385425245157719840052431687426507323712199265501115580412

def g13DistP : ℕ := 45114470612536300500243201754288975642390380123306789293001581061178314341484602173982292983920328858420895413976827081650779239925120121132418773422721390726983047560822814425192746407709276152992504259956814065963120327213656518456597113457469642076402964434350035287946552655920154755502146761323028288160427223638498413122416977819114855203035523361816116995251768534389947820758631389252685538959819743448208222164562733420925976883600585613408177362001383786768198220134731690252223840783180771104531535043415778505305522395595011476994991864740603249143344328458109727502817195322502692633911150613928505334441520210891221906966412542583031555898713334743969793456111263027330175579993391327147342250194572150111445416682235514054549060208346101900336340322952048442218726820938077266941614138066908231331383665161102180264000313273882535923974445631511924747353064761344

def g13ParP : ℕ := 1356824297098662961696545144034370532708515864340774092195991287275310321976971730915818738223095126929727484689493184723379612124678773795566206552420305293362577164737330520916555151437481005558976437097451431544218921038428646275310934356238042684911584674565127200166626987312673145393159679001324564540953641593323615378792671299254580424398285597578762021548177373893881180265787609385468048259386070609733021184838779750517110862849907227886293352521111538809894411258239829325723470174785356517762530921482848588597179417987470139806761854356546914484805369042036654547581495787175274352124543104452027650411537275740269439507016698113360021637954604401094967602945757821295052394580415789482961406284876471694388539547854827320545079632083054672125230326841036123049410807852471521588109942212138681170656585860379156103321355755514621396994327705124706404208914187299221414691705735955110183843580658876822897248804311013090876810882057598046446015895618291759102195081211868461121604576643665853818700124493424919429828722978840512075380324346933809104407228149203467976520408695476045179175312521130807682608523821038950607165347000342404258155475366892454574952153515741511741115015727206522209031475145168372242518647131585230471340519916894473727778867265162951695388762725653735545682506575702349875940189863717713397262082406658371637911810966298755778916555470227089982269166450172903697868689323988092746849555976652981881632856366197787798164281830623349328152872122855174862739922150212222103031763008288569664779004732476788155502542548867188935073783442322081160774206720408298468238788818588572671924073641146445190175125581827035947698324394931700214078993336895428154913325352684235246345951420017935144757531608167865817794217534821248759638072499705373565634231525115491961649450329823920470192288872474016362260900309300056526751518809201789060893201618181829671471182700059736394450316398017349439682718152334591815222838803434987945570402344753551123625083665594747973657330883197511935732812520714647367381196589203756303718220473541434258437942843099508856066341935658319454675746724092118782882639099297100944151119097908530081620704266682123452982120810545152

def g13GenP : ℕ := 2354942882230141400637436307169941376547044178544678758747242770611399292307650286116444172326953821543335682018421112785622458415602529476301136104388351971079677752807407587255255169071527896310421704555758748061979760

theorem g13Cls_rd (c : ℕ) : CFSG.Monster.GMS.Griess13.OrbTab.cls.getD c 0 = g13ClsP / 2 ^ (2 * c) % 2 ^ 2 := by
  have e : g13PackW 2 CFSG.Monster.GMS.Griess13.OrbTab.cls = g13ClsP := by decide +kernel
  rw [← e]
  exact g13PackW_getD 2 _ (by decide +kernel) c

theorem g13Dist_rd (c : ℕ) : CFSG.Monster.GMS.Griess13.OrbTab.dist.getD c 0 = g13DistP / 2 ^ (4 * c) % 2 ^ 4 := by
  have e : g13PackW 4 CFSG.Monster.GMS.Griess13.OrbTab.dist = g13DistP := by decide +kernel
  rw [← e]
  exact g13PackW_getD 4 _ (by decide +kernel) c

theorem g13Par_rd (c : ℕ) : CFSG.Monster.GMS.Griess13.OrbTab.par.getD c 0 = g13ParP / 2 ^ (10 * c) % 2 ^ 10 := by
  have e : g13PackW 10 CFSG.Monster.GMS.Griess13.OrbTab.par = g13ParP := by decide +kernel
  rw [← e]
  exact g13PackW_getD 10 _ (by decide +kernel) c

theorem g13Gen_rd (c : ℕ) : CFSG.Monster.GMS.Griess13.OrbTab.gen.getD c 0 = g13GenP / 2 ^ (1 * c) % 2 ^ 1 := by
  have e : g13PackW 1 CFSG.Monster.GMS.Griess13.OrbTab.gen = g13GenP := by decide +kernel
  rw [← e]
  exact g13PackW_getD 1 _ (by decide +kernel) c

theorem orbitClassR_vec {c : ℕ} (hc : c < 729) :
    orbitClassR (vecOfCode c) = g13ClsP / 2 ^ (2 * c) % 2 ^ 2 := by
  unfold orbitClassR
  rw [codeOf_vecOfCode c hc, cls_get, g13Cls_rd]

theorem matNs_get :
    ∀ s : Fin 2, ∀ i j : Fin 6, ((matNs[s.val]!)[i.val]!)[j.val]! = (actN s i j).val := by
  decide +kernel

theorem stepN_eq (A : Array (Array ℕ)) (c : ℕ) :
    stepN A c = ∑ i : Fin 6, 3 ^ i.val *
      ((∑ j : Fin 6, (A[i.val]!)[j.val]! * (c / 3 ^ j.val % 3)) % 3) := by
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  simp only [stepN, hr, List.foldl_cons, List.foldl_nil, Fin.sum_univ_six]
  simp

theorem mulVec_val (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (c : ℕ) (i : Fin 6) :
    ((M *ᵥ vecOfCode c) i).val = (∑ j : Fin 6, (M i j).val * (c / 3 ^ j.val % 3)) % 3 := by
  have h : (M *ᵥ vecOfCode c) i = ((∑ j : Fin 6, (M i j).val * (c / 3 ^ j.val % 3) : ℕ) : ZMod 3) := by
    simp [Matrix.mulVec, dotProduct, vecOfCode, Nat.cast_sum, Nat.cast_mul]
  rw [h, ZMod.val_natCast]

theorem vecOfCode_stepS :
    ∀ s : Fin 2, ∀ c < 729, vecOfCode (stepS s.val c) = actN s *ᵥ vecOfCode c := by
  intro s c _
  funext i
  apply ZMod.val_injective
  simp only [vecOfCode, ZMod.val_natCast, Nat.mod_mod]
  rw [stepS, stepN_eq]
  simp only [matNs_get, ← mulVec_val]
  exact digit6 (fun k => ((actN s *ᵥ vecOfCode c) k).val) (fun k => ZMod.val_lt _) i

theorem matNs_lit : matNs = #[#[#[1, 0, 0, 0, 0, 0], #[1, 2, 1, 2, 2, 2], #[2, 2, 0, 1, 2, 2],
    #[1, 2, 2, 0, 1, 0], #[2, 1, 1, 1, 1, 1], #[0, 2, 2, 1, 1, 1]],
    #[#[1, 2, 0, 0, 0, 2], #[0, 1, 0, 0, 0, 0], #[0, 0, 2, 0, 1, 2],
    #[2, 2, 0, 2, 0, 2], #[1, 2, 2, 1, 2, 2], #[2, 0, 1, 2, 2, 1]]] := by
  decide +kernel

theorem g13RepCode_eq (k : ℕ) : repCode k = if k = 1 then 247 else if k = 2 then 9 else 1 := by
  unfold repCode repVec
  split_ifs <;> decide +kernel

def g13StepT (s c : ℕ) : ℕ :=
  if s = 0 then
    stepN #[#[1, 0, 0, 0, 0, 0], #[1, 2, 1, 2, 2, 2], #[2, 2, 0, 1, 2, 2],
      #[1, 2, 2, 0, 1, 0], #[2, 1, 1, 1, 1, 1], #[0, 2, 2, 1, 1, 1]] c
  else if s = 1 then
    stepN #[#[1, 2, 0, 0, 0, 2], #[0, 1, 0, 0, 0, 0], #[0, 0, 2, 0, 1, 2],
      #[2, 2, 0, 2, 0, 2], #[1, 2, 2, 1, 2, 2], #[2, 0, 1, 2, 2, 1]] c
  else stepS s c

theorem g13StepS_T (s c : ℕ) : stepS s c = g13StepT s c := by
  unfold g13StepT
  split_ifs with h0 h1
  · subst h0
    unfold stepS
    rw [matNs_lit]
    rfl
  · subst h1
    unfold stepS
    rw [matNs_lit]
    rfl
  · rfl

theorem orbCheckR_true : orbCheckR = true := by
  unfold orbCheckR
  simp only [orbTabR, toArray_get!, g13Cls_rd, g13Dist_rd, g13Par_rd, g13Gen_rd, g13RepCode_eq,
    g13StepS_T]
  decide +kernel

theorem orbitClassR_repw : ∀ k : Fin 12, orbitClassR (repw k) = 1 := by decide +kernel

theorem orbitClassR_w1 : orbitClassR w1 = 1 := by decide +kernel

theorem orbitClassR_wB : orbitClassR wB = 2 := by decide +kernel

theorem orbitClassR_wC : orbitClassR wC = 3 := by decide +kernel

theorem negCls_all :
    (List.range 729).all (fun c => g13ClsP / 2 ^ (2 * codeOf (-vecOfCode c)) % 2 ^ 2 ==
      g13ClsP / 2 ^ (2 * c) % 2 ^ 2) = true := by
  decide +kernel

theorem orbitClassR_neg : ∀ w : Fin 6 → ZMod 3, orbitClassR (-w) = orbitClassR w := by
  refine forall_vec fun c hc => ?_
  rw [orbitClassR_vec hc]
  unfold orbitClassR
  rw [cls_get, g13Cls_rd]
  exact beq_iff_eq.1 (List.all_eq_true.1 negCls_all c (List.mem_range.2 hc))

theorem one_codes :
    ∀ c < 729, c ≠ 0 → g13ClsP / 2 ^ (2 * c) % 2 ^ 2 = 1 →
      ∃ k : Fin 12, ∃ a : ZMod 3, a ≠ 0 ∧ codeOf (a • repw k) = c := by
  decide +kernel

theorem orbitClassR_one_spec :
    ∀ w : Fin 6 → ZMod 3, w ≠ 0 → orbitClassR w = 1 →
      ∃ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ w = c • repw k := by
  refine forall_vec fun c hc h0 h1 => ?_
  rw [orbitClassR_vec hc] at h1
  obtain ⟨k, a, ha, e⟩ := one_codes c hc ((vecOfCode_ne_zero_iff hc).1 h0) h1
  exact ⟨k, a, ha, by rw [← e, vecOfCode_codeOf]⟩

theorem card_ne_zero_cls (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => P (orbitClassR w)).card =
      ((Finset.range 729).filter fun c => c ≠ 0 ∧ P (g13ClsP / 2 ^ (2 * c) % 2 ^ 2)).card := by
  have e : (Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter (fun w => P (orbitClassR w)) =
      Finset.univ.filter fun w => w ≠ 0 ∧ P (orbitClassR w) := by
    ext w
    simp
  rw [e, card_codeVec]
  refine congrArg Finset.card (Finset.filter_congr fun c hc => ?_)
  rw [Finset.mem_range] at hc
  rw [vecOfCode_ne_zero_iff hc, orbitClassR_vec hc]

theorem card_orbitClassR_one :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 1).card = 24 := by
  rw [card_ne_zero_cls (fun n => n = 1)]
  decide +kernel

theorem card_orbitClassR_two :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 2).card = 264 := by
  rw [card_ne_zero_cls (fun n => n = 2)]
  decide +kernel

theorem card_orbitClassR_three :
    ((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 3).card = 440 := by
  rw [card_ne_zero_cls (fun n => n = 3)]
  decide +kernel

theorem card_orbIdx (P : Fin 3 → Prop) [DecidablePred P] :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ P (orbitIndexR w)).card =
      ((Finset.range 729).filter fun c => c ≠ 0 ∧
        P (if g13ClsP / 2 ^ (2 * c) % 2 ^ 2 = 1 then 0
          else if g13ClsP / 2 ^ (2 * c) % 2 ^ 2 = 2 then 1 else 2)).card := by
  rw [card_codeVec]
  refine congrArg Finset.card (Finset.filter_congr fun c hc => ?_)
  rw [Finset.mem_range] at hc
  rw [vecOfCode_ne_zero_iff hc, orbitIndexR, orbitClassR_vec hc]

theorem card_orbitIndexR_zero :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 0).card = 24 := by
  rw [card_orbIdx (fun i => i = 0)]
  decide +kernel

theorem card_orbitIndexR_one :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 1).card = 264 := by
  rw [card_orbIdx (fun i => i = 1)]
  decide +kernel

theorem card_orbitIndexR_two :
    (Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 2).card = 440 := by
  rw [card_orbIdx (fun i => i = 2)]
  decide +kernel

theorem repw_ne_zero : ∀ k : Fin 12, repw k ≠ 0 := by decide +kernel

end CertificateChecks.KernelG13

end
