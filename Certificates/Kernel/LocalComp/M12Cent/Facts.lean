module

public import Certificates.Kernel.LocalComp.M12Cent.Data
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Cent

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem img_of_bind {n w : Nat} {g : Equiv.Perm (Fin n)} {l : List Nat} {P : Nat}
    (hl : l = imageList g) (h : bindListK n w P l = true) :
    imageList g = (unpack n w P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem getD_map_of_lt {α β : Type} (f : α → β) {ws : List α} (d : α) (e : β) {j : Nat}
    (hj : j < ws.length) : (ws.map f).getD j e = f (ws.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
    List.getElem_map]

theorem gens_img {n w : Nat} (hsz : szOK n w = true) {gA gB : Equiv.Perm (Fin n)} {A B : Nat}
    (hA : imageList gA = (unpack n w A).toList) (hB : imageList gB = (unpack n w B).toList)
    (pA : permOK n w (mask w) (n * w) A (pinvS n w (mask w) A) = true)
    (pB : permOK n w (mask w) (n * w) B (pinvS n w (mask w) B) = true)
    {ws : List (List Int)} {S : Nat → Nat}
    (h : allN ws.length (fun j => bAnd(abOK (ws.getD j []), Nat.beq (abWordK n w (mask w)
      (pidn n w) A (pinvS n w (mask w) A) B (pinvS n w (mask w) B) (ws.getD j [])) (S j))) =
      true) :
    ∀ j < ws.length, imageList ((ws.map (evalCodes [gA, gB])).getD j 1) =
      (unpack n w (S j)).toList := by
  intro j hj
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec h j hj)
  rw [getD_map_of_lt _ [] 1 hj, abWordK_rep hsz hA hB pA pB h1, Nat.eq_of_beq_eq_true h2]

theorem gens_img_push {n w : Nat} {ws : List (List Int)} {gA gB s : Equiv.Perm (Fin n)}
    {S : Nat → Nat} {P : Nat}
    (hw : ∀ j < ws.length, imageList ((ws.map (evalCodes [gA, gB])).getD j 1) =
      (unpack n w (S j)).toList)
    (hs : imageList s = (unpack n w P).toList) (hP : Nat.beq (S ws.length) P = true) :
    ∀ j < (ws.map (evalCodes [gA, gB]) ++ [s]).length,
      imageList ((ws.map (evalCodes [gA, gB]) ++ [s]).getD j 1) = (unpack n w (S j)).toList := by
  intro j hj
  simp only [List.length_append, List.length_map, List.length_singleton] at hj
  rcases Nat.lt_or_ge j ws.length with h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact hw j h
  · have e : j = ws.length := by omega
    subst e
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.sub_self]
    rw [Nat.eq_of_beq_eq_true hP]
    exact hs

theorem reps_img {n w : Nat} (hsz : szOK n w = true) {gs : List (Equiv.Perm (Fin n))}
    {S SI : Nat → Nat} (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack n w (S j)).toList)
    (hp : allN gs.length (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {ws : List (List Int)} {Ps : Nat → Nat}
    (hk : allN ws.length (fun i => bAnd(lettersK gs.length (ws.getD i []),
      Nat.beq (wordK n w (mask w) (pidn n w) S SI (ws.getD i [])) (Ps i))) = true) :
    ∀ i < ws.length, imageList ((ws.map (evalCodes gs)).getD i 1) =
      (unpack n w (Ps i)).toList := by
  intro i hi
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hi)
  rw [getD_map_of_lt _ [] 1 hi, evalCodes_img hsz hg (fun j hj => allN_spec hp j hj) hid h1,
    Nat.eq_of_beq_eq_true h2]

theorem ord_all {n w e c : Nat} (hsz : szOK n w = true) {reps : List (Equiv.Perm (Fin n))}
    {Ps : Nat → Nat} (hr : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack n w (Ps i)).toList)
    (hk : allN c (fun i => bAnd(canonK n w (mask w) (n * w) (Ps i),
      ordIs n w (mask w) (pidn n w) (Ps i) (e - 1))) = true) (he : 0 < e) :
    (reps.map toTable).all (ordTest n e) = true := by
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ht
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hr'
  have hic : i < c := hr ▸ hi'
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hic)
  have himg := hi i hic
  rw [List.getD_eq_getElem _ _ hi'] at himg
  exact ordTest_of_ordIs hsz himg h1 he h2

theorem comm_all {n w : Nat} {gs : List (Equiv.Perm (Fin n))} {S : Nat → Nat}
    {h : Equiv.Perm (Fin n)} {H : Nat}
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack n w (S j)).toList)
    (hh : imageList h = (unpack n w H).toList)
    (hk : allN gs.length (fun j => commK n w (mask w) (n * w) (S j) H) = true) :
    (gs.all fun g => commT n (toTable g) (toTable h)) = true := by
  rw [List.all_eq_true]
  intro g hg'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg hh (allN_spec hk j hj)

theorem sz12 : szOK 12 4 = true := by quickRfl
theorem sz24 : szOK 24 5 = true := by quickRfl

theorem LA_eq : LA = imageList m12gA := by decide
theorem LB_eq : LB = imageList m12gB := by decide
theorem LA1_eq : LA1 = imageList m12A1 := by decide
theorem LB1_eq : LB1 = imageList m12B1 := by decide
theorem LS_eq : LS = imageList m12Sigma := by decide
theorem LZ_eq : LZ = imageList (blockHom (permZ, permZ)) := by decide

theorem bA : bindListK 12 4 PA LA = true := by quickRfl
theorem bB : bindListK 12 4 PB LB = true := by quickRfl
theorem bA1 : bindListK 24 5 PA1 LA1 = true := by quickRfl
theorem bB1 : bindListK 24 5 PB1 LB1 = true := by quickRfl
theorem bS : bindListK 24 5 PS LS = true := by quickRfl
theorem bZ : bindListK 24 5 PZ LZ = true := by quickRfl

theorem imgA : imageList m12gA = (unpack 12 4 PA).toList := img_of_bind LA_eq bA
theorem imgB : imageList m12gB = (unpack 12 4 PB).toList := img_of_bind LB_eq bB
theorem imgA1 : imageList m12A1 = (unpack 24 5 PA1).toList := img_of_bind LA1_eq bA1
theorem imgB1 : imageList m12B1 = (unpack 24 5 PB1).toList := img_of_bind LB1_eq bB1
theorem imgS : imageList m12Sigma = (unpack 24 5 PS).toList := img_of_bind LS_eq bS
theorem imgZ : imageList (blockHom (permZ, permZ)) = (unpack 24 5 PZ).toList :=
  img_of_bind LZ_eq bZ

theorem pA : permOK 12 4 (mask 4) (12 * 4) PA (pinvS 12 4 (mask 4) PA) = true := by quickRfl
theorem pB : permOK 12 4 (mask 4) (12 * 4) PB (pinvS 12 4 (mask 4) PB) = true := by quickRfl
theorem pA1 : permOK 24 5 (mask 5) (24 * 5) PA1 (pinvS 24 5 (mask 5) PA1) = true := by quickRfl
theorem pB1 : permOK 24 5 (mask 5) (24 * 5) PB1 (pinvS 24 5 (mask 5) PB1) = true := by quickRfl

theorem one12 : imageList (1 : Equiv.Perm (Fin 12)) = (unpack 12 4 (pidn 12 4)).toList := by
  decide
theorem one24 : imageList (1 : Equiv.Perm (Fin 24)) = (unpack 24 5 (pidn 24 5)).toList := by
  decide
theorem cOne12 : canonK 12 4 (mask 4) (12 * 4) One12 = true := by quickRfl
theorem cOne24 : canonK 24 5 (mask 5) (24 * 5) One24 = true := by quickRfl

theorem kG1 : allN m12CentWords1.length (fun j => bAnd(abOK (m12CentWords1.getD j []),
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB
      (pinvS 12 4 (mask 4) PB) (m12CentWords1.getD j [])) (C1.S j))) = true := by quickRfl

theorem kG3 : allN m12CentWords2.length (fun j => bAnd(abOK (m12CentWords2.getD j []),
    Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB
      (pinvS 12 4 (mask 4) PB) (m12CentWords2.getD j [])) (C3.S j))) = true := by quickRfl

theorem kG2 : allN m12CentWords1.length (fun j => bAnd(abOK (m12CentWords1.getD j []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) PA1 (pinvS 24 5 (mask 5) PA1) PB1
      (pinvS 24 5 (mask 5) PB1) (m12CentWords1.getD j [])) (Q2.S j))) = true := by quickRfl

theorem kG4 : allN q4GWords.length (fun j => bAnd(abOK (q4GWords.getD j []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) PA1 (pinvS 24 5 (mask 5) PA1) PB1
      (pinvS 24 5 (mask 5) PB1) (q4GWords.getD j [])) (Q4.S j))) = true := by quickRfl

theorem kG5 : allN m12SigmaCentWords.length (fun j => bAnd(abOK (m12SigmaCentWords.getD j []),
    Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) PA1 (pinvS 24 5 (mask 5) PA1) PB1
      (pinvS 24 5 (mask 5) PB1) (m12SigmaCentWords.getD j [])) (Q5.S j))) = true := by quickRfl

theorem kS2 : Nat.beq (Q2.S m12CentWords1.length) PS = true := by quickRfl
theorem kS4 : Nat.beq (Q4.S q4GWords.length) PS = true := by quickRfl
theorem kS5 : Nat.beq (Q5.S m12SigmaCentWords.length) PS = true := by quickRfl

theorem q4Gens_eq : q4Gens = q4GWords.map (evalCodes [m12A1, m12B1]) ++ [m12Sigma] := by
  rw [q4Gens, q4GWords, List.map_map]
  rfl

theorem img1 : ∀ j < k1Gens.length, imageList (k1Gens.getD j 1) = (unpack 12 4 (C1.S j)).toList :=
  gens_img sz12 imgA imgB pA pB kG1

theorem img3 : ∀ j < k3Gens.length, imageList (k3Gens.getD j 1) = (unpack 12 4 (C3.S j)).toList :=
  gens_img sz12 imgA imgB pA pB kG3

theorem img2 : ∀ j < q2Gens.length, imageList (q2Gens.getD j 1) = (unpack 24 5 (Q2.S j)).toList :=
  gens_img_push (gens_img sz24 imgA1 imgB1 pA1 pB1 kG2) imgS kS2

theorem img4 : ∀ j < q4Gens.length, imageList (q4Gens.getD j 1) = (unpack 24 5 (Q4.S j)).toList :=
  q4Gens_eq ▸ gens_img_push (gens_img sz24 imgA1 imgB1 pA1 pB1 kG4) imgS kS4

theorem img5 : ∀ j < q5Gens.length, imageList (q5Gens.getD j 1) = (unpack 24 5 (Q5.S j)).toList :=
  gens_img_push (gens_img sz24 imgA1 imgB1 pA1 pB1 kG5) imgS kS5

theorem chain1 : ChainK 12 4 k1Gens m12CentChainWords1 (#v[0, 1, 2] : Vector (Fin 12) 3)
    C1.S C1.SI C1.LR C1.TR C1.TRI 8 C1.BP 1 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img1, by decide, C1.head, C1.hl, by norm_num, C1.hs⟩

theorem chain3 : ChainK 12 4 k3Gens m12CentChainWords2 (#v[0, 1, 2] : Vector (Fin 12) 3)
    C3.S C3.SI C3.LR C3.TR C3.TRI 5 C3.BP 1 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img3, by decide, C3.head, C3.hl, by norm_num, C3.hs⟩

theorem chain2 : ChainK 24 5 q2Gens q2Words (#v[0, 1, 2] : Vector (Fin 24) 3)
    Q2.S Q2.SI Q2.LR Q2.TR Q2.TRI 9 Q2.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img2, by decide, Q2.head, Q2.hl, by norm_num, Q2.hs⟩

theorem chain4 : ChainK 24 5 q4Gens q4Words (#v[0, 1, 2] : Vector (Fin 24) 3)
    Q4.S Q4.SI Q4.LR Q4.TR Q4.TRI 7 Q4.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img4, by decide, Q4.head, Q4.hl, by norm_num, Q4.hs⟩

theorem chain5 : ChainK 24 5 q5Gens q5Words (#v[0, 1, 2] : Vector (Fin 24) 3)
    Q5.S Q5.SI Q5.LR Q5.TR Q5.TRI 6 Q5.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img5, by decide, Q5.head, Q5.hl, by norm_num, Q5.hs⟩

theorem cnt1 : (cosetOrderTables m12CentQ1 1 4).length = R1.N :=
  (chainK_cosetCount (by decide) (by decide) chain1 one12 cOne12 (by norm_num) (by norm_num)
    (by decide) X1.hc).trans (by decide)

theorem cnt3 : (cosetOrderTables m12CentQ2 1 4).length = R3.N :=
  (chainK_cosetCount (by decide) (by decide) chain3 one12 cOne12 (by norm_num) (by norm_num)
    (by decide) X3.hc).trans (by decide)

theorem cnt2 : (cosetOrderTables q2Q 1 4).length = R2.N :=
  (chainK_cosetCount (by decide) (by decide) chain2 one24 cOne24 (by norm_num) (by norm_num)
    (by decide) X2.hc).trans (by decide)

theorem cnt4 : (cosetOrderTables q4Q 1 4).length = R4.N :=
  (chainK_cosetCount (by decide) (by decide) chain4 one24 cOne24 (by norm_num) (by norm_num)
    (by decide) X4.hc).trans (by decide)

theorem cnt5 : (cosetOrderTables q5Q 1 4).length = 0 :=
  (chainK_cosetCount (by decide) (by decide) chain5 one24 cOne24 (by norm_num) (by norm_num)
    (by decide) X5.hc).trans (by decide)

theorem kP1 : allN k1Gens.length (fun j => permOK 12 4 (mask 4) (12 * 4) (C1.S j) (C1.SI j)) =
    true := by quickRfl
theorem kP3 : allN k3Gens.length (fun j => permOK 12 4 (mask 4) (12 * 4) (C3.S j) (C3.SI j)) =
    true := by quickRfl
theorem kP2 : allN q2Gens.length (fun j => permOK 24 5 (mask 5) (24 * 5) (Q2.S j) (Q2.SI j)) =
    true := by quickRfl
theorem kP4 : allN q4Gens.length (fun j => permOK 24 5 (mask 5) (24 * 5) (Q4.S j) (Q4.SI j)) =
    true := by quickRfl
theorem kP5 : allN q5Gens.length (fun j => permOK 24 5 (mask 5) (24 * 5) (Q5.S j) (Q5.SI j)) =
    true := by quickRfl

theorem kC1 : allN k1Gens.length (fun j => bAnd(canonK 12 4 (mask 4) (12 * 4) (C1.S j),
    canonK 12 4 (mask 4) (12 * 4) (C1.SI j))) = true := by quickRfl
theorem kC3 : allN k3Gens.length (fun j => bAnd(canonK 12 4 (mask 4) (12 * 4) (C3.S j),
    canonK 12 4 (mask 4) (12 * 4) (C3.SI j))) = true := by quickRfl
theorem kC2 : allN q2Gens.length (fun j => bAnd(canonK 24 5 (mask 5) (24 * 5) (Q2.S j),
    canonK 24 5 (mask 5) (24 * 5) (Q2.SI j))) = true := by quickRfl
theorem kC4 : allN q4Gens.length (fun j => bAnd(canonK 24 5 (mask 5) (24 * 5) (Q4.S j),
    canonK 24 5 (mask 5) (24 * 5) (Q4.SI j))) = true := by quickRfl
theorem kC5 : allN q5Gens.length (fun j => bAnd(canonK 24 5 (mask 5) (24 * 5) (Q5.S j),
    canonK 24 5 (mask 5) (24 * 5) (Q5.SI j))) = true := by quickRfl

theorem kW1 : allN k1Words.length (fun i => bAnd(lettersK k1Gens.length (k1Words.getD i []),
    Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) C1.S C1.SI (k1Words.getD i []))
      (R1.E (lget R1.OFF i)))) = true := by quickRfl
theorem kW3 : allN k3Words.length (fun i => bAnd(lettersK k3Gens.length (k3Words.getD i []),
    Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) C3.S C3.SI (k3Words.getD i []))
      (R3.E (lget R3.OFF i)))) = true := by quickRfl
theorem kW2 : allN q2RWords.length (fun i => bAnd(lettersK q2Gens.length (q2RWords.getD i []),
    Nat.beq (wordK 24 5 (mask 5) (pidn 24 5) Q2.S Q2.SI (q2RWords.getD i []))
      (R2.E (lget R2.OFF i)))) = true := by quickRfl
theorem kW4 : allN q4RWords.length (fun i => bAnd(lettersK q4Gens.length (q4RWords.getD i []),
    Nat.beq (wordK 24 5 (mask 5) (pidn 24 5) Q4.S Q4.SI (q4RWords.getD i []))
      (R4.E (lget R4.OFF i)))) = true := by quickRfl

theorem kO1 : allN k1Words.length (fun i => bAnd(canonK 12 4 (mask 4) (12 * 4) (R1.E (lget R1.OFF i)),
    ordIs 12 4 (mask 4) (pidn 12 4) (R1.E (lget R1.OFF i)) (4 - 1))) = true := by quickRfl
theorem kO3 : allN k3Words.length (fun i => bAnd(canonK 12 4 (mask 4) (12 * 4) (R3.E (lget R3.OFF i)),
    ordIs 12 4 (mask 4) (pidn 12 4) (R3.E (lget R3.OFF i)) (4 - 1))) = true := by quickRfl
theorem kO2 : allN q2RWords.length (fun i => bAnd(canonK 24 5 (mask 5) (24 * 5) (R2.E (lget R2.OFF i)),
    ordIs 24 5 (mask 5) (pidn 24 5) (R2.E (lget R2.OFF i)) (4 - 1))) = true := by quickRfl
theorem kO4 : allN q4RWords.length (fun i => bAnd(canonK 24 5 (mask 5) (24 * 5) (R4.E (lget R4.OFF i)),
    ordIs 24 5 (mask 5) (pidn 24 5) (R4.E (lget R4.OFF i)) (4 - 1))) = true := by quickRfl

theorem kOff1 : offOK R1.CS R1.OFF R1.N = true := by quickRfl
theorem kOff3 : offOK R3.CS R3.OFF R3.N = true := by quickRfl
theorem kOff2 : offOK R2.CS R2.OFF R2.N = true := by quickRfl
theorem kOff4 : offOK R4.CS R4.OFF R4.N = true := by quickRfl
theorem kOff5 : offOK [] [] 0 = true := by quickRfl

theorem kPos1 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R1.CS = true := by quickRfl
theorem kPos3 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R3.CS = true := by quickRfl
theorem kPos2 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R2.CS = true := by quickRfl
theorem kPos4 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R4.CS = true := by quickRfl

theorem kR1 : allN R1.N (repK 12 4 C1.S C1.SI 4 R1.CS R1.OFF R1.CI R1.E R1.P R1.L R1.K R1.S
    R1.SI R1.N 1000) = true := by quickRfl
theorem kR3 : allN R3.N (repK 12 4 C3.S C3.SI 3 R3.CS R3.OFF R3.CI R3.E R3.P R3.L R3.K R3.S
    R3.SI R3.N 1000) = true := by quickRfl
theorem kR2 : allN R2.N (repK 24 5 Q2.S Q2.SI 5 R2.CS R2.OFF R2.CI R2.E R2.P R2.L R2.K R2.S
    R2.SI R2.N 1000) = true := by quickRfl
theorem kR4 : allN R4.N (repK 24 5 Q4.S Q4.SI 4 R4.CS R4.OFF R4.CI R4.E R4.P R4.L R4.K R4.S
    R4.SI R4.N 1000) = true := by quickRfl

theorem kM2 : allN q2Gens.length (fun j => commK 24 5 (mask 5) (24 * 5) (Q2.S j) PA1) = true := by
  quickRfl
theorem kM4 : allN q4Gens.length (fun j => commK 24 5 (mask 5) (24 * 5) (Q4.S j) PZ) = true := by
  quickRfl
theorem kM5 : allN q5Gens.length (fun j => commK 24 5 (mask 5) (24 * 5) (Q5.S j) PS) = true := by
  quickRfl

theorem kN2 : Nat.beq (ordK Q2.LR 3) 384 = true := by quickRfl
theorem kN4 : Nat.beq (ordK Q4.LR 3) 480 = true := by quickRfl
theorem kN5 : Nat.beq (ordK Q5.LR 3) 240 = true := by quickRfl

theorem checkK1_eq : checkK1 = true := by
  have hri := reps_img sz12 img1 kP1 one12 kW1
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables m12CentQ1 1 4)
    (by decide : k1Gens.length = 4) img1 (fun j hj => allN_spec kP1 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC1 j hj)) (by decide : k1Reps.length = R1.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff1 kPos1 cnt1
    (fun j hj => allN_spec kR1 j hj)
  have h3 := ord_all sz12 (reps := k1Reps) (e := 4) (by decide)
    (fun i hi => hri i hi) kO1 (by norm_num)
  unfold checkK1 listTables
  rw [h1, h2, h3]
  decide

theorem checkK3_eq : checkK3 = true := by
  have hri := reps_img sz12 img3 kP3 one12 kW3
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables m12CentQ2 1 4)
    (by decide : k3Gens.length = 3) img3 (fun j hj => allN_spec kP3 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC3 j hj)) (by decide : k3Reps.length = R3.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff3 kPos3 cnt3
    (fun j hj => allN_spec kR3 j hj)
  have h3 := ord_all sz12 (reps := k3Reps) (e := 4) (by decide)
    (fun i hi => hri i hi) kO3 (by norm_num)
  unfold checkK3 listTables
  rw [h1, h2, h3]
  decide

theorem checkQ2_eq : checkQ2 = true := by
  obtain ⟨hc, ho⟩ : q2Q.check = true ∧ q2Q.orderCertificate = ordK Q2.LR 3 :=
    chainK_check (by decide) (by decide) chain2
  have hri := reps_img sz24 img2 kP2 one24 kW2
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables q2Q 1 4)
    (by decide : q2Gens.length = 5) img2 (fun j hj => allN_spec kP2 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC2 j hj)) (by decide : q2Reps.length = R2.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff2 kPos2 cnt2
    (fun j hj => allN_spec kR2 j hj)
  have h3 := ord_all sz24 (reps := q2Reps) (e := 4) (by decide)
    (fun i hi => hri i hi) kO2 (by norm_num)
  have h4 := comm_all img2 imgA1 kM2
  unfold checkQ2 listTables
  rw [hc, ho, Nat.eq_of_beq_eq_true kN2, h1, h2, h3, h4]
  decide

theorem checkQ4_eq : checkQ4 = true := by
  obtain ⟨hc, ho⟩ : q4Q.check = true ∧ q4Q.orderCertificate = ordK Q4.LR 3 :=
    chainK_check (by decide) (by decide) chain4
  have hri := reps_img sz24 img4 kP4 one24 kW4
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables q4Q 1 4)
    (by decide : q4Gens.length = 4) img4 (fun j hj => allN_spec kP4 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC4 j hj)) (by decide : q4Reps.length = R4.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff4 kPos4 cnt4
    (fun j hj => allN_spec kR4 j hj)
  have h3 := ord_all sz24 (reps := q4Reps) (e := 4) (by decide)
    (fun i hi => hri i hi) kO4 (by norm_num)
  have h4 := comm_all img4 imgZ kM4
  unfold checkQ4 listTables
  rw [hc, ho, Nat.eq_of_beq_eq_true kN4, h1, h2, h3, h4]
  decide

theorem checkQ5_eq : checkQ5 = true := by
  obtain ⟨hc, ho⟩ : q5Q.check = true ∧ q5Q.orderCertificate = ordK Q5.LR 3 :=
    chainK_check (by decide) (by decide) chain5
  obtain ⟨h1, -⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables q5Q 1 4)
    (reps := []) (CS := []) (OFF := []) (N := 0) (CI := fun _ => 0) (E := fun _ => 0)
    (P := fun _ => 0) (L := fun _ => 0) (K := fun _ => 0) (S := fun _ => 0) (SI := fun _ => 0)
    (by decide : q5Gens.length = 4) img5 (fun j hj => allN_spec kP5 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC5 j hj)) rfl (fun i hi => absurd hi (by simp))
    kOff5 rfl cnt5 (fun j hj => absurd hj (by omega))
  have h4 := comm_all img5 imgS kM5
  unfold checkQ5 listTables
  rw [hc, ho, Nat.eq_of_beq_eq_true kN5, h4]
  simpa using h1

theorem facts : (checkK1 = true) ∧ (checkK3 = true) ∧ (checkQ2 = true) ∧ (checkQ4 = true) ∧
    (checkQ5 = true) :=
  ⟨checkK1_eq, checkK3_eq, checkQ2_eq, checkQ4_eq, checkQ5_eq⟩

end CertificateChecks.KernelLC.M12Cent

end
