module

public import Certificates.Data.Kernel.MonsterB.Sp8Span
public import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.TwoA.Co2Inv.Data

public section

namespace CertificateChecks.Sp8Rows3073

open CFSG.KC.KDense CFSG.KC.Rep4371Row CFSG.KC.Sp8Span CFSG.Monster.B CFSG.Monster.B.TwoA.Co2Inv

@[expose] noncomputable def P0 : Nat := nat_lit 858949293449307062001231508273203232
@[expose] noncomputable def P1 : Nat := nat_lit 773025645656475952206417415184156704
@[expose] noncomputable def P2 : Nat := nat_lit 601512028743074303593415300685596704
@[expose] noncomputable def P3 : Nat := nat_lit 515922713892533379094243404675123232
@[expose] noncomputable def P4 : Nat := nat_lit 639237837286367304290900785894623264
@[expose] noncomputable def P5 : Nat := nat_lit 858949331863002823319395354394331168
@[expose] noncomputable def P6 : Nat := nat_lit 815574042220565238508866290310055968
@[expose] noncomputable def P7 : Nat := nat_lit 813265984686454672680271770342722592
@[expose] noncomputable def P8 : Nat := nat_lit 727676631497327073735880915801966593

@[expose] noncomputable def BT0 : Nat := nat_lit 326750922023807900844292541155013053104188
@[expose] noncomputable def BT1 : Nat := nat_lit 326671183932999325898038583800217903284284
@[expose] noncomputable def BT2 : Nat := nat_lit 326671204707267264749650478955760051273788
@[expose] noncomputable def BT3 : Nat := nat_lit 326750963577409432815049566394872089526332
@[expose] noncomputable def BT4 : Nat := nat_lit 79852377123519937059095045476500881468
@[expose] noncomputable def BT5 : Nat := nat_lit 5795753095163299400861748478560280349003834
@[expose] noncomputable def BT6 : Nat := nat_lit 79843287434890999654727880244512145468
@[expose] noncomputable def BT7 : Nat := nat_lit 326671163153665732778893453715901014851644
@[expose] noncomputable def BT8 : Nat := nat_lit 5708640886511322095468339943891984393146502

theorem pe0 : ∀ i < 24, pe P0 i = fPerms[0]![i]! := by decide +kernel
theorem pe1 : ∀ i < 24, pe P1 i = fPerms[1]![i]! := by decide +kernel
theorem pe2 : ∀ i < 24, pe P2 i = fPerms[2]![i]! := by decide +kernel
theorem pe3 : ∀ i < 24, pe P3 i = fPerms[3]![i]! := by decide +kernel
theorem pe4 : ∀ i < 24, pe P4 i = fPerms[4]![i]! := by decide +kernel
theorem pe5 : ∀ i < 24, pe P5 i = fPerms[5]![i]! := by decide +kernel
theorem pe6 : ∀ i < 24, pe P6 i = fPerms[6]![i]! := by decide +kernel
theorem pe7 : ∀ i < 24, pe P7 i = fPerms[7]![i]! := by decide +kernel
theorem pe8 : ∀ i < 24, pe P8 i = fPerms[8]![i]! := by decide +kernel

theorem bt0 : betaTabT P0 = BT0 := by decide +kernel
theorem bt1 : betaTabT P1 = BT1 := by decide +kernel
theorem bt2 : betaTabT P2 = BT2 := by decide +kernel
theorem bt3 : betaTabT P3 = BT3 := by decide +kernel
theorem bt4 : betaTabT P4 = BT4 := by decide +kernel
theorem bt5 : betaTabT P5 = BT5 := by decide +kernel
theorem bt6 : betaTabT P6 = BT6 := by decide +kernel
theorem bt7 : betaTabT P7 = BT7 := by decide +kernel
theorem bt8 : betaTabT P8 = BT8 := by decide +kernel

theorem kappa63 : ∀ j < 9, Model.kappaN fPerms[j]! 63 = false := by decide +kernel

theorem perm0 : spanEqT [eYT 3, ePermT P0 BT0 0, ePauliT 0 0 0]
    [ePermT P0 BT0 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm1 : spanEqT [eYT 3, ePermT P1 BT1 0, ePauliT 0 0 0]
    [ePermT P1 BT1 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm2 : spanEqT [eYT 3, ePermT P2 BT2 0, ePauliT 0 0 0]
    [ePermT P2 BT2 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm3 : spanEqT [eYT 3, ePermT P3 BT3 0, ePauliT 0 0 0]
    [ePermT P3 BT3 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm4 : spanEqT [eYT 3, ePermT P4 BT4 0, ePauliT 0 0 0]
    [ePermT P4 BT4 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm5 : spanEqT [eYT 3, ePermT P5 BT5 0, ePauliT 0 0 0]
    [ePermT P5 BT5 0, ePauliT 0 0 0, ePauliT 1 63 0, eYT 3] = true := by decide +kernel
theorem perm6 : spanEqT [eYT 3, ePermT P6 BT6 0, ePauliT 0 0 0]
    [ePermT P6 BT6 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm7 : spanEqT [eYT 3, ePermT P7 BT7 0, ePauliT 0 0 0]
    [ePermT P7 BT7 0, ePauliT 0 0 0, ePauliT 0 0 0, eYT 3] = true := by decide +kernel
theorem perm8 : spanEqT [eYT 3, ePermT P8 BT8 0, ePauliT 0 0 0]
    [ePermT P8 BT8 0, ePauliT 0 0 0, ePauliT 1 63 0, eYT 3] = true := by decide +kernel

theorem sign0 : spanEqT (eYT 3 :: [2, 1].map eYT) ([2, 1].map eYT ++ [ePauliT 0 0 0, eYT 3]) =
    true := by decide +kernel
theorem sign1 : spanEqT (eYT 3 :: [4, 1].map eYT) ([4, 1].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign2 : spanEqT (eYT 3 :: [8, 1].map eYT) ([8, 1].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign3 : spanEqT (eYT 3 :: [16, 1].map eYT) ([16, 1].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign4 : spanEqT (eYT 3 :: [32, 1].map eYT) ([32, 1].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign5 : spanEqT (eYT 3 :: [64].map eYT) ([64].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign6 : spanEqT (eYT 3 :: [128, 1].map eYT) ([128, 1].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign7 : spanEqT (eYT 3 :: [256].map eYT) ([256].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign8 : spanEqT (eYT 3 :: [512].map eYT) ([512].map eYT ++ [ePauliT 1 63 0, eYT 3]) =
    true := by decide +kernel
theorem sign9 : spanEqT (eYT 3 :: [1024].map eYT) ([1024].map eYT ++ [ePauliT 0 0 0, eYT 3]) =
    true := by decide +kernel
theorem sign10 : spanEqT (eYT 3 :: [2048].map eYT) ([2048].map eYT ++ [ePauliT 0 0 0, eYT 3]) =
    true := by decide +kernel

end CertificateChecks.Sp8Rows3073

end
