module

public import CFSG.Quasithin.H13.L32NG9MInputs
public import CFSG.Certificates.Kernel.Mat8KSound
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CertificateChecks.G9MK

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.G9MCert CFSG.KC.Mat8K CFSG.KC.Loop

@[expose] noncomputable def mv8S (A : List ℕ) (v : ℕ) : ℕ := strictN v (mv8K A)

@[expose] noncomputable def mul8S (A B : List ℕ) : List ℕ := B.map (mv8S A)

@[expose] noncomputable def evalWS (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mul8S (gens.getD i one8) acc) one8

theorem mv8_toS (A : List ℕ) (v : ℕ) : mv8 A v = mv8S A v := by
  have e : strictN v (mv8K A) = mv8K A v := by cases v <;> rfl
  rw [mv8S, e, mv8K_eq]

theorem mul8_toS (A B : List ℕ) : mul8 A B = mul8S A B := by
  have e : mv8 A = mv8S A := funext (mv8_toS A)
  rw [mul8, mul8S, e]

theorem evalW_toS (gens : List (List ℕ)) (w : List ℕ) : evalW gens w = evalWS gens w := by
  simp only [evalW, evalWS, mul8_toS]

@[expose] noncomputable def pow8K (A : List ℕ) (n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) one8 (fun _ acc => mul8S A acc) n

theorem pow8_toS (A : List ℕ) : ∀ n, pow8 A n = pow8K A n
  | 0 => rfl
  | n + 1 => by
    have e : pow8K A (n + 1) = mul8S A (pow8K A n) := rfl
    rw [e, ← pow8_toS A n, pow8, mul8_toS]

@[expose] noncomputable def invsK : List (List ℕ) := all4.filter fun x => mul8S (blk x) (blk x) == one8

@[expose] noncomputable def ords5K : List (List ℕ) :=
  all4.filter fun y => pow8K (blk y) 5 == one8 && blk y != one8

@[expose] noncomputable def relS5K (X Y : List ℕ) : Bool :=
  pow8K (mul8S X Y) 4 == one8 && pow8K (mul8S (mul8S (mul8S X (pow8K Y 4)) X) Y) 3 == one8 &&
    pow8K (mul8S (mul8S (mul8S X (pow8K Y 3)) X) (pow8K Y 2)) 2 == one8

@[expose] noncomputable def relA5K (X Y : List ℕ) : Bool := pow8K (mul8S X Y) 3 == one8

@[expose] noncomputable def inv4K (c : List ℕ) : Option (List ℕ) :=
  one4.mapM fun b => (List.range 16).find? fun u => mv8S c u == b

@[expose] noncomputable def verifyCK (x y c ic xm ym : List ℕ) : Bool :=
  validB (blk c) && validB (blk ic) && mul8S (blk c) (blk ic) == one8 &&
    mul8S (blk ic) (blk c) == one8 && mul8S (blk x) (blk c) == mul8S (blk c) (blk xm) &&
    mul8S (blk y) (blk c) == mul8S (blk c) (blk ym) && mul8S (blk c) s0c == mul8S s0c (blk c) &&
    mul8S (blk c) s1c == mul8S s1c (blk c)

@[expose] noncomputable def spinMatK (x y : List ℕ) (m : Model) (v : ℕ) : List ℕ :=
  mul8S (m.2.2.1.map fun w => mv8S (evalWS [blk x, blk y] w) v) m.2.2.2

@[expose] noncomputable def tryCK (x y : List ℕ) (m : Model) (c : List ℕ) :
    Option (List ℕ × List ℕ × List ℕ × List ℕ) :=
  if mul8S (blk x) (blk c) == mul8S (blk c) (blk m.1) then
    match inv4K c with
    | some ic => if verifyCK x y c ic m.1 m.2.1 then some (c, ic, m.1, m.2.1) else none
    | none => none
  else none

@[expose] noncomputable def findConjK (x y : List ℕ) (ms : List Model) :
    Option (List ℕ × List ℕ × List ℕ × List ℕ) :=
  ms.findSome? fun m => (List.range 15).findSome? fun i => tryCK x y m (spinMatK x y m (i + 1))

@[expose] noncomputable def spinYK (y : List ℕ) : List ℕ :=
  let v₁ := mv8S y 1
  let v₂ := mv8S y v₁
  [1, v₁, v₂, mv8S y v₂]

@[expose] noncomputable def verifyYK (y d di : List ℕ) : Bool :=
  validB (blk d) && validB (blk di) && mul8S (blk d) (blk di) == one8 &&
    mul8S (blk di) (blk d) == one8 && mul8S (blk y) (blk d) == mul8S (blk d) (blk y0) &&
    mul8S (blk d) s0c == mul8S s0c (blk d) && mul8S (blk d) s1c == mul8S s1c (blk d)

@[expose] noncomputable def normCheckK : Bool :=
  ords5K.all fun y =>
    match inv4K (spinYK y) with
    | some di => verifyYK y (spinYK y) di
    | none => false

@[expose] noncomputable def s5CheckK : Bool :=
  invsK.all fun x => !relS5K (blk x) (blk y0) || (findConjK x y0 modelsS5).isSome

@[expose] noncomputable def a5CheckK : Bool :=
  invsK.all fun x => x == one4 || !relA5K (blk x) (blk y0) || (findConjK x y0 modelsA5).isSome

@[expose] noncomputable def g9mCheckK : Bool := normCheckK && s5CheckK && a5CheckK

theorem invs_eq : invs = invsK := by
  simp only [invs, invsK, mul8_toS]

theorem ords5_eq : ords5 = ords5K := by
  simp only [ords5, ords5K, pow8_toS]

theorem relS5_eq : relS5 = relS5K := by
  funext X Y
  simp only [relS5, relS5K, pow8_toS, mul8_toS]

theorem relA5_eq : relA5 = relA5K := by
  funext X Y
  simp only [relA5, relA5K, pow8_toS, mul8_toS]

theorem inv4_eq : inv4 = inv4K := by
  funext c
  simp only [inv4, inv4K, mv8_toS]

theorem verifyC_eq : verifyC = verifyCK := by
  funext x y c ic xm ym
  simp only [verifyC, verifyCK, mul8_toS]

theorem spinMat_eq : spinMat = spinMatK := by
  funext x y m v
  simp only [spinMat, spinMatK, mul8_toS, mv8_toS, evalW_toS]

theorem tryC_eq : tryC = tryCK := by
  funext x y m c
  unfold tryC tryCK
  rw [inv4_eq, verifyC_eq]
  simp only [mul8_toS]
  cases inv4K c <;> rfl

theorem findConj_eq : findConj = findConjK := by
  funext x y ms
  simp only [findConj, findConjK, tryC_eq, spinMat_eq]

theorem spinY_eq : spinY = spinYK := by
  funext y
  simp only [spinY, spinYK, mv8_toS]

theorem verifyY_eq : verifyY = verifyYK := by
  funext y d di
  simp only [verifyY, verifyYK, mul8_toS]

theorem normCheck_eq : normCheck = normCheckK := by
  unfold normCheck normCheckK
  rw [ords5_eq, inv4_eq, spinY_eq, verifyY_eq]
  exact congrArg (List.all ords5K) (funext fun y => by cases inv4K (spinYK y) <;> rfl)

theorem g9mCheck_eq : g9mCheck = g9mCheckK := by
  simp only [g9mCheck, g9mCheckK, normCheck_eq, s5Check, s5CheckK, a5Check, a5CheckK,
    invs_eq, relS5_eq, relA5_eq, findConj_eq]

end CertificateChecks.G9MK
