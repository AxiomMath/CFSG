module

public import CFSG.Certificates.Kernel.Misc.T46Sound
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Kernel.Misc.Unitary
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.PK.MiscPerm
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Misc.O73Sound
public import Mathlib

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.T46

open CFSG.KC.Misc.T46 CFSG.F4.Native CFSG.Sporadic.Fi22.Native
open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73

theorem bWS : CFSG.KC.Misc.T46.wordStrings = WC.map CFSG.KC.Misc.O73.strOf := by kernelRfl

@[expose] noncomputable def xyStr (w : List Nat) : String :=
  String.ofList (w.map fun z => Bool.rec (motive := fun _ => Char) 'y' 'x' (Nat.beq z 1))

theorem bTWs : t46TvWords = (TW.map xyStr).toArray.map t46XYWord := by kernelRfl

theorem tw12 : (TW.all fun w => w.all fun z => z == 1 || z == 2) = true := by quickRfl

theorem xyStr_map {L : List (List Nat)}
    (h : (L.all fun w => w.all fun z => z == 1 || z == 2) = true) :
    (L.map xyStr).map t46XYWord = L.map (List.map Int.ofNat) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw
  have h := List.all_eq_true.1 (List.all_eq_true.1 h w hw)
  simp only [Function.comp_apply, xyStr, t46XYWord, String.toList_ofList, List.map_map]
  apply List.map_congr_left
  intro z hz
  rcases Bool.or_eq_true_iff.1 (h z hz) with h1 | h1 <;> simp at h1 <;> subst h1 <;> rfl

theorem bTW : t46TvWords = (TW.map (List.map Int.ofNat)).toArray := by
  rw [bTWs, List.map_toArray, xyStr_map tw12]

theorem pts : ptsK CFSG.KD.Misc.Unitary.UL UP = true := by quickRfl
theorem letters : lettersK GP WC LP = true := by quickRfl
theorem trees : treesK LP [0, 1, 3, 9, 45] 11 O1 Pa1 La1 O2 Pa2 La2 = true := by quickRfl
theorem xy : xyK GP [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] = true := by quickRfl

@[expose] noncomputable def ofChunks (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor c (Nat.shiftLeft ih 280)) l

@[expose] noncomputable def XL : Nat := ofChunks [
  495597965520460765787207224161657023184529462570586850344023387422497610857075721393,
  791857582560094187166400828691800066171553516247541023719471455355021644570200143121,
  1155509732275315166329480973917828185749460212252122582288276559637859015987909628297,
  118011954191877881345470118835072246531666373530242438917322392720619049076921638010,
  721599641647222267612405533951380297637069732586486704088040155755913361707315075327,
  161296218465234355717994576287681604459890664210838639668615130815567888608197528938,
  129715198652323186609869633707854116037447639132040620916047557037524785686192271808,
  919156649857525250069386150788389359757956605648119218752005553438551473177575676269,
  698881052428327664942604370738019204227544791030068458674930442835738292357467376022,
  972261585151033562535939929177176839637145657435973186065335934740120356463732694393,
  178387147038273789557500066010208860379758084049683223738539921611565495368441817576,
  956986343383131542542075101311640220590902086364967433050733505528335226357782369737,
  337950404645354004063862185738143439105821275873652921663392159992396537189510918660,
  334165401887464454873228573514762546633713917579483640841479258761436068180698271931,
  450038559909166327680694078480357118362018813394866122815008585277661574787399475220,
  634241077304219065174413944180634069626305617666004534720556681415326557566180538617,
  400668766562706828631712332232137365892144356743012233580982933741845159872779268264,
  613352148201325005625622941295031922068375476802669426169499851480985662936294096959,
  1008397180948765705848283105972102228861919356678325251727816711457922307337763336527,
  1015993148342164444130282750101978324041757113567626274227354194753498085857794074140,
  1114686137527551230267120667290252293106022867603040052253853651207662342280859760160,
  1311172264376258504289230634935741329664316328788007809670667895396134048621119779460,
  1093864083784007117933444983906237382025543479096692652921834217007281832888989556379,
  246699233838472546039954212169381760555734456883184935646161862244806064119614150220,
  1008516238278695330687992661010142916656424416241795175073602222]

@[expose] noncomputable def YL : Nat := ofChunks [
  879599396306717403134721535648626311110408568584046489918787818164649632153255268006,
  562616785973531995902330902591275911635802206350961464716237357219556594828948678687,
  666455464389950285179330749016075133528709684216560330667589159593592473526890404210,
  1186256635324846398949043351241677633333772894627890867394519770444791558886119340448,
  969563833960938576116853939040705386882655127355002113647040877465819083622776619288,
  687818301144020692140414408866989752086632865354502721044340384170195237496531045557,
  736218352094004419117378211750613140314028338940877764450783206050798308313941465573,
  249529707282574868562897618357843279809016160898773758124035769022755026783730904112,
  668263751014957312932729885494468206486084825917825935650106117747581455660209421575,
  575893098009876148695923023732480226567746513939694532730212801962890528085495075941,
  877287992228708823376157618331576072919210174601873057411654950364814910675723313515,
  55408720253873334510480856383969890684008279526237607686234802993514657181894059229,
  213115461786738825052139283491650325642840298995447659639040589129437203022729150924,
  428099897101659470862779869057823951759850142543223225632996960143487673276697996662,
  437621884021321709750255438984464692154299762804274148461800957629994803206734202514,
  1144111988477306503412292233053107619868145166430684650958278418076518446862027101616,
  753446170905139600857808029396364284213853070242765303274407524909489760854533590656,
  797083614069197798182608302212177382384518502628217253086368940983919897297991111966,
  509390987251700791700166615058354594538509121116866341122317262177200860422889148683,
  944929401379903296016265624440119364206996826880385612155203152329190902063819786659,
  113130141368768179681954626462565885198681513943793249873830759078547410371295711404,
  1257867456614441970317258081986426630680096749174701855156491292475744748873520356527,
  63451541039570222500726978001760314426641464335127170274432778370040634188045429967,
  1048358114242159261169048387989994265899192216683627865285644886790684199890568261274,
  916145127817077266264751071367179784036293840670239570435568937]

abbrev xw : List Int := [30, 33, 16, 12, 9, 39, 39]

abbrev yw : List Int := [41, 46, 21, 23, 36]

theorem hXL : powP 3 (wordG GP xw) = XL := Nat.eq_of_beq_eq_true (by quickRfl)

theorem hYL : powP 2 (wordG GP yw) = YL := Nat.eq_of_beq_eq_true (by quickRfl)

theorem twLen : Nat.beq (relPK.lenLLN TW) 46 = true := by quickRfl

theorem tvWordsK_of {GP : List Nat} {xw yw : List Int} {TW : List (List Nat)} {X Y : Nat}
    (k : Nat) (hX : powP 3 (wordG GP xw) = X) (hY : powP 2 (wordG GP yw) = Y)
    (hl : Nat.beq (relPK.lenLLN TW) 46 = true)
    (h : impB (Nat.blt k 46) (Nat.beq (wordXY X Y (nthL TW k)) (wordM7.nthN GP k)) = true) :
    tvWordsK GP xw yw TW k 1 = true := by
  have hL : ∀ (y : Nat) (f : Nat → Bool), letB y f = f y := fun y f => by cases y <;> rfl
  have hA : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
  rw [tvWordsK, hX, hY]
  simp only [hL, hA, hl, Bool.true_and]
  change (impB (Nat.blt (Nat.add k 0) 46)
    (Nat.beq (wordXY X Y (nthL TW (Nat.add k 0))) (wordM7.nthN GP (Nat.add k 0))) && true) = true
  rw [Nat.add_eq, Nat.add_zero, h]
  rfl

@[expose] noncomputable def evalXY (X Y : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => at' 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1)) (ih x)) w

theorem evalXY_eq (X Y : Nat) (w : List Nat) (x : Nat) :
    evalXY X Y w x = w.foldr (fun z y => CFSG.KS.PK.fd 10 (if z = 1 then X else Y) y) x := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    change at' 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1)) (evalXY X Y w x) = _
    rw [ih, CFSG.KS.PK.at'_eq, List.foldr_cons]
    by_cases hz : z = 1
    · subst hz
      rfl
    · have hb : Nat.beq z 1 = false := by
        cases h : Nat.beq z 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hz
      simp [hb, hz]

@[expose] noncomputable def sylStep (z : Nat) (acc : List Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (2 :: acc)
    (List.rec (motive := fun _ => List Nat) [1]
      (fun a r _ => Bool.rec (motive := fun _ => List Nat) (1 :: a :: r)
        (List.rec (motive := fun _ => List Nat) [3]
          (fun b s _ => Bool.rec (motive := fun _ => List Nat) (3 :: b :: s) (4 :: s) (Nat.beq b 2))
          r)
        (Nat.beq a 2)) acc)
    (Nat.beq z 1)

@[expose] noncomputable def sylXY (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun z _ ih => sylStep z ih) w

@[expose] noncomputable def selXY (X Y A B z : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) B A (Nat.beq z 3)) Y
      (Nat.beq z 2))
    X (Nat.beq z 1)

@[expose] noncomputable def evalSy (X Y A B : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => at' 10 (selXY X Y A B z) (ih x)) w

@[expose] noncomputable def tvSy (X Y : Nat) (w : List Nat) (G : Nat) : Bool :=
  letB X fun X => letB Y fun Y => letB (compP 693 10 X Y) fun A =>
    letB (compP 693 10 A Y) fun B => letB G fun G =>
      andB (Nat.blt G (Nat.shiftLeft 1 (Nat.mul 10 693)))
        (allN 693 fun x => Nat.beq (evalSy X Y A B (sylXY w) x) (at' 10 G x))

theorem fdComp (t u : Nat) {v : Nat} (hv : v < 693) :
    CFSG.KS.PK.fd 10 (compP 693 10 t u) v = CFSG.KS.PK.fd 10 t (CFSG.KS.PK.fd 10 u v) := by
  rw [CFSG.KS.PK.compP_eq, CFSG.KS.PK.fd_enc (fun i _ => CFSG.KS.PK.fd_lt _ _ _) hv]

section Syl

variable {X Y : Nat} (hX : ∀ v < 693, CFSG.KS.PK.fd 10 X v < 693)
  (hY : ∀ v < 693, CFSG.KS.PK.fd 10 Y v < 693)
include hX hY

theorem selXY_lt (z : Nat) {v : Nat} (hv : v < 693) :
    CFSG.KS.PK.fd 10 (selXY X Y (compP 693 10 X Y) (compP 693 10 (compP 693 10 X Y) Y) z) v
      < 693 := by
  have hA : ∀ v < 693, CFSG.KS.PK.fd 10 (compP 693 10 X Y) v < 693 := fun v hv => by
    rw [fdComp _ _ hv]
    exact hX _ (hY v hv)
  have hB : ∀ v < 693, CFSG.KS.PK.fd 10 (compP 693 10 (compP 693 10 X Y) Y) v < 693 :=
    fun v hv => by
      rw [fdComp _ _ hv]
      exact hA _ (hY v hv)
  unfold selXY
  cases Nat.beq z 1
  · cases Nat.beq z 2
    · cases Nat.beq z 3
      · exact hB v hv
      · exact hA v hv
    · exact hY v hv
  · exact hX v hv

theorem evalSy_lt (w : List Nat) {x : Nat} (hx : x < 693) :
    evalSy X Y (compP 693 10 X Y) (compP 693 10 (compP 693 10 X Y) Y) w x < 693 := by
  induction w with
  | nil => exact hx
  | cons z w ih =>
    change at' 10 _ _ < 693
    rw [CFSG.KS.PK.at'_eq]
    exact selXY_lt hX hY z ih

theorem sylStep_eval (z : Nat) (acc : List Nat) {x : Nat} (hx : x < 693) :
    evalSy X Y (compP 693 10 X Y) (compP 693 10 (compP 693 10 X Y) Y) (sylStep z acc) x =
      at' 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1))
        (evalSy X Y (compP 693 10 X Y) (compP 693 10 (compP 693 10 X Y) Y) acc x) := by
  have hE := fun w => evalSy_lt hX hY w hx
  unfold sylStep
  cases Nat.beq z 1
  · rfl
  · rcases acc with _ | ⟨a, r⟩
    · rfl
    · dsimp only
      cases ha : Nat.beq a 2
      · rfl
      · obtain rfl : a = 2 := Nat.eq_of_beq_eq_true ha
        rcases r with _ | ⟨b, s⟩
        · change at' 10 (compP 693 10 X Y) x = at' 10 X (at' 10 Y x)
          simp only [CFSG.KS.PK.at'_eq]
          exact fdComp _ _ hx
        · dsimp only
          cases hb : Nat.beq b 2
          · change at' 10 (compP 693 10 X Y) (evalSy _ _ _ _ (b :: s) x) =
              at' 10 X (at' 10 Y (evalSy _ _ _ _ (b :: s) x))
            simp only [CFSG.KS.PK.at'_eq]
            exact fdComp _ _ (hE _)
          · obtain rfl : b = 2 := Nat.eq_of_beq_eq_true hb
            change at' 10 (compP 693 10 (compP 693 10 X Y) Y) (evalSy _ _ _ _ s x) =
              at' 10 X (at' 10 Y (at' 10 Y (evalSy _ _ _ _ s x)))
            simp only [CFSG.KS.PK.at'_eq]
            rw [fdComp _ _ (hE _), fdComp _ _ (hY _ (hE _))]

theorem evalSy_syl (w : List Nat) {x : Nat} (hx : x < 693) :
    evalSy X Y (compP 693 10 X Y) (compP 693 10 (compP 693 10 X Y) Y) (sylXY w) x =
      evalXY X Y w x := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    change evalSy _ _ _ _ (sylStep z (sylXY w)) x =
      at' 10 (Bool.rec (motive := fun _ => Nat) Y X (Nat.beq z 1)) (evalXY X Y w x)
    rw [sylStep_eval hX hY z _ hx, ih]

theorem tvSy_spec {G : Nat} {w : List Nat} (h : tvSy X Y w G = true) : wordXY X Y w = G := by
  simp only [tvSy, CFSG.KS.PK.letB_eq, CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.blt_eq,
    CFSG.KS.PK.allN_lqt_iff, Nat.beq_eq] at h
  obtain ⟨hG, hpt⟩ := h
  have e : Nat.shiftLeft 1 (10 * 693) = 2 ^ (10 * 693) := Nat.one_shiftLeft _
  rw [e] at hG
  rw [CFSG.KS.PK.wordXY_eq, ← CFSG.KS.PK.enc_fd hG]
  exact CFSG.KS.PK.enc_congr fun x hx => by
    rw [← CFSG.KS.PK.at'_eq, ← hpt x hx, evalSy_syl hX hY w hx, evalXY_eq]

end Syl

theorem rngXL : allN 693 (fun i => Nat.blt (at' 10 XL i) 693) = true := by quickRfl

theorem rngYL : allN 693 (fun i => Nat.blt (at' 10 YL i) 693) = true := by quickRfl

theorem rng_of {P : Nat} (h : allN 693 (fun i => Nat.blt (at' 10 P i) 693) = true) :
    ∀ v < 693, CFSG.KS.PK.fd 10 P v < 693 := fun v hv => by
  have h1 := (CFSG.KS.PK.allN_lqt_iff.1 h) v hv
  rw [Nat.blt_eq, CFSG.KS.PK.at'_eq] at h1
  exact h1

theorem tvXYS (k : Nat) (h : tvSy XL YL (nthL TW k) (wordM7.nthN GP k) = true) :
    tvWordsK GP xw yw TW k 1 = true := by
  refine tvWordsK_of k hXL hYL twLen ?_
  rw [tvSy_spec (rng_of rngXL) (rng_of rngYL) h, Nat.beq_refl]
  cases Nat.blt k 46 <;> rfl

@[expose] noncomputable def t46F4 (x y : Nat) : Nat :=
  Nat.mod (Nat.shiftRight 2625168384 (Nat.mul 2 (Nat.add (Nat.mul 4 x) y))) 4

@[expose] noncomputable def t46Herm (c d : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc
    (t46F4 (crdK c i) (letN (crdK d i) fun e => t46F4 e e))) 6

@[expose] noncomputable def t46Scale (a c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc
    (Nat.mul (t46F4 a (crdK c i)) (Nat.pow 4 i))) 6

@[expose] noncomputable def t46Norm (c : Nat) : Nat := letN (leadK c) fun a => t46Scale (f4K a a) c

@[expose] noncomputable def t46TvQ (v x : Nat) : Nat := Nat.xor x (t46Scale (t46Herm x v) v)

@[expose] noncomputable def t46GenQ (UP v G : Nat) : Bool :=
  letB G fun G => andB (permK 693 10 G) <| allN 693 fun x =>
    letB (t46Norm (t46TvQ v (at' 12 UP x))) fun d => letB (at' 10 G x) fun j =>
      andB (Nat.blt j 693) (Nat.beq (at' 12 UP j) d)

@[expose] noncomputable def gensOL (UL : List Nat) (UP : Nat) (GP : List Nat) (lo n : Nat) : Bool :=
  andB (Nat.beq (lenN (gensK UL)) 46) <| andB (Nat.beq (lenN GP) 46) <|
    allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k 46)
      (t46GenQ UP (wordM7.nthN (gensK UL) k) (wordM7.nthN GP k))

theorem f4K_lt4 (x y : Nat) : f4K x y < 4 := by
  have h1 : ∀ a b : Nat, Nat.add (Nat.mod a 2) (Nat.mul 2 (Nat.mod b 2)) < 4 := fun a b => by
    change a % 2 + 2 * (b % 2) < 4
    omega
  exact h1 _ _

theorem crdK_lt4 (c i : Nat) : crdK c i < 4 := Nat.mod_lt _ (by decide)

theorem t46F4_eq {x y : Nat} (hx : x < 4) (hy : y < 4) : t46F4 x y = f4K x y := by
  interval_cases x <;> interval_cases y <;> rfl

theorem hermK_lt4 (c d : Nat) : hermK c d < 4 := by
  have h : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc
      (f4K (crdK c i) (letN (crdK d i) fun e => f4K e e))) n < 4 := fun n => by
    induction n with
    | zero => exact Nat.zero_lt_succ 3
    | succ n ih => exact Nat.xor_lt_two_pow (n := 2) ih (f4K_lt4 _ _)
  exact h 6

theorem t46Herm_eq (c d : Nat) : t46Herm c d = hermK c d := by
  simp only [t46Herm, hermK, CFSG.KS.PK.letN_eq, t46F4_eq, crdK_lt4, f4K_lt4]

theorem t46Scale_eq {a : Nat} (c : Nat) (ha : a < 4) : t46Scale a c = scaleK a c := by
  simp only [t46Scale, scaleK, t46F4_eq, ha, crdK_lt4]

theorem t46Norm_eq (c : Nat) : t46Norm c = normK c := by
  simp only [t46Norm, normK, CFSG.KS.PK.letN_eq, t46Scale_eq _ (f4K_lt4 _ _)]

theorem t46TvQ_eq (v x : Nat) : t46TvQ v x = tvK v x := by
  simp only [t46TvQ, tvK, t46Herm_eq, t46Scale_eq _ (hermK_lt4 _ _)]

theorem t46GenQ_eq (UP v G : Nat) : t46GenQ UP v G = genK UP v G := by
  simp only [t46GenQ, genK, t46Norm_eq, t46TvQ_eq]

theorem gensOL_eq (UL : List Nat) (UP : Nat) (GP : List Nat) (lo n : Nat) :
    gensOL UL UP GP lo n = gensOK UL UP GP lo n := by
  simp only [gensOL, gensOK, t46GenQ_eq]

theorem t46GenOf {k : Nat} (h : gensOL CFSG.KD.Misc.Unitary.UL UP GP k 1 = true) :
    gensOK CFSG.KD.Misc.Unitary.UL UP GP k 1 = true := (gensOL_eq _ _ _ _ _).symm.trans h

theorem gen0 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 0 1 = true := t46GenOf (by quickRfl)
theorem gen1 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 1 1 = true := t46GenOf (by quickRfl)
theorem gen2 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 2 1 = true := t46GenOf (by quickRfl)
theorem gen3 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 3 1 = true := t46GenOf (by quickRfl)
theorem gen4 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 4 1 = true := t46GenOf (by quickRfl)
theorem gen5 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 5 1 = true := t46GenOf (by quickRfl)
theorem gen6 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 6 1 = true := t46GenOf (by quickRfl)
theorem gen7 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 7 1 = true := t46GenOf (by quickRfl)
theorem gen8 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 8 1 = true := t46GenOf (by quickRfl)
theorem gen9 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 9 1 = true := t46GenOf (by quickRfl)
theorem gen10 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 10 1 = true := t46GenOf (by quickRfl)
theorem gen11 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 11 1 = true := t46GenOf (by quickRfl)
theorem gen12 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 12 1 = true := t46GenOf (by quickRfl)
theorem gen13 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 13 1 = true := t46GenOf (by quickRfl)
theorem gen14 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 14 1 = true := t46GenOf (by quickRfl)
theorem gen15 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 15 1 = true := t46GenOf (by quickRfl)
theorem gen16 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 16 1 = true := t46GenOf (by quickRfl)
theorem gen17 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 17 1 = true := t46GenOf (by quickRfl)
theorem gen18 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 18 1 = true := t46GenOf (by quickRfl)
theorem gen19 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 19 1 = true := t46GenOf (by quickRfl)
theorem gen20 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 20 1 = true := t46GenOf (by quickRfl)
theorem gen21 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 21 1 = true := t46GenOf (by quickRfl)
theorem gen22 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 22 1 = true := t46GenOf (by quickRfl)
theorem gen23 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 23 1 = true := t46GenOf (by quickRfl)
theorem gen24 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 24 1 = true := t46GenOf (by quickRfl)
theorem gen25 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 25 1 = true := t46GenOf (by quickRfl)
theorem gen26 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 26 1 = true := t46GenOf (by quickRfl)
theorem gen27 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 27 1 = true := t46GenOf (by quickRfl)
theorem gen28 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 28 1 = true := t46GenOf (by quickRfl)
theorem gen29 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 29 1 = true := t46GenOf (by quickRfl)
theorem gen30 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 30 1 = true := t46GenOf (by quickRfl)
theorem gen31 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 31 1 = true := t46GenOf (by quickRfl)
theorem gen32 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 32 1 = true := t46GenOf (by quickRfl)
theorem gen33 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 33 1 = true := t46GenOf (by quickRfl)
theorem gen34 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 34 1 = true := t46GenOf (by quickRfl)
theorem gen35 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 35 1 = true := t46GenOf (by quickRfl)
theorem gen36 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 36 1 = true := t46GenOf (by quickRfl)
theorem gen37 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 37 1 = true := t46GenOf (by quickRfl)
theorem gen38 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 38 1 = true := t46GenOf (by quickRfl)
theorem gen39 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 39 1 = true := t46GenOf (by quickRfl)
theorem gen40 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 40 1 = true := t46GenOf (by quickRfl)
theorem gen41 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 41 1 = true := t46GenOf (by quickRfl)
theorem gen42 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 42 1 = true := t46GenOf (by quickRfl)
theorem gen43 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 43 1 = true := t46GenOf (by quickRfl)
theorem gen44 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 44 1 = true := t46GenOf (by quickRfl)
theorem gen45 : gensOK CFSG.KD.Misc.Unitary.UL UP GP 45 1 = true := t46GenOf (by quickRfl)
theorem tv0 : tvWordsK GP xw yw TW 0 1 = true := tvXYS 0 (by quickRfl)
theorem tv1 : tvWordsK GP xw yw TW 1 1 = true := tvXYS 1 (by quickRfl)
theorem tv2 : tvWordsK GP xw yw TW 2 1 = true := tvXYS 2 (by quickRfl)
theorem tv3 : tvWordsK GP xw yw TW 3 1 = true := tvXYS 3 (by quickRfl)
theorem tv4 : tvWordsK GP xw yw TW 4 1 = true := tvXYS 4 (by quickRfl)
theorem tv5 : tvWordsK GP xw yw TW 5 1 = true := tvXYS 5 (by quickRfl)
theorem tv6 : tvWordsK GP xw yw TW 6 1 = true := tvXYS 6 (by quickRfl)
theorem tv7 : tvWordsK GP xw yw TW 7 1 = true := tvXYS 7 (by quickRfl)
theorem tv8 : tvWordsK GP xw yw TW 8 1 = true := tvXYS 8 (by quickRfl)
theorem tv9 : tvWordsK GP xw yw TW 9 1 = true := tvXYS 9 (by quickRfl)
theorem tv10 : tvWordsK GP xw yw TW 10 1 = true := tvXYS 10 (by quickRfl)
theorem tv11 : tvWordsK GP xw yw TW 11 1 = true := tvXYS 11 (by quickRfl)
theorem tv12 : tvWordsK GP xw yw TW 12 1 = true := tvXYS 12 (by quickRfl)
theorem tv13 : tvWordsK GP xw yw TW 13 1 = true := tvXYS 13 (by quickRfl)
theorem tv14 : tvWordsK GP xw yw TW 14 1 = true := tvXYS 14 (by quickRfl)
theorem tv15 : tvWordsK GP xw yw TW 15 1 = true := tvXYS 15 (by quickRfl)
theorem tv16 : tvWordsK GP xw yw TW 16 1 = true := tvXYS 16 (by quickRfl)
theorem tv17 : tvWordsK GP xw yw TW 17 1 = true := tvXYS 17 (by quickRfl)
theorem tv18 : tvWordsK GP xw yw TW 18 1 = true := tvXYS 18 (by quickRfl)
theorem tv19 : tvWordsK GP xw yw TW 19 1 = true := tvXYS 19 (by quickRfl)
theorem tv20 : tvWordsK GP xw yw TW 20 1 = true := tvXYS 20 (by quickRfl)
theorem tv21 : tvWordsK GP xw yw TW 21 1 = true := tvXYS 21 (by quickRfl)
theorem tv22 : tvWordsK GP xw yw TW 22 1 = true := tvXYS 22 (by quickRfl)
theorem tv23 : tvWordsK GP xw yw TW 23 1 = true := tvXYS 23 (by quickRfl)
theorem tv24 : tvWordsK GP xw yw TW 24 1 = true := tvXYS 24 (by quickRfl)
theorem tv25 : tvWordsK GP xw yw TW 25 1 = true := tvXYS 25 (by quickRfl)
theorem tv26 : tvWordsK GP xw yw TW 26 1 = true := tvXYS 26 (by quickRfl)
theorem tv27 : tvWordsK GP xw yw TW 27 1 = true := tvXYS 27 (by quickRfl)
theorem tv28 : tvWordsK GP xw yw TW 28 1 = true := tvXYS 28 (by quickRfl)
theorem tv29 : tvWordsK GP xw yw TW 29 1 = true := tvXYS 29 (by quickRfl)
theorem tv30 : tvWordsK GP xw yw TW 30 1 = true := tvXYS 30 (by quickRfl)
theorem tv31 : tvWordsK GP xw yw TW 31 1 = true := tvXYS 31 (by quickRfl)
theorem tv32 : tvWordsK GP xw yw TW 32 1 = true := tvXYS 32 (by quickRfl)
theorem tv33 : tvWordsK GP xw yw TW 33 1 = true := tvXYS 33 (by quickRfl)
theorem tv34 : tvWordsK GP xw yw TW 34 1 = true := tvXYS 34 (by quickRfl)
theorem tv35 : tvWordsK GP xw yw TW 35 1 = true := tvXYS 35 (by quickRfl)
theorem tv36 : tvWordsK GP xw yw TW 36 1 = true := tvXYS 36 (by quickRfl)
theorem tv37 : tvWordsK GP xw yw TW 37 1 = true := tvXYS 37 (by quickRfl)
theorem tv38 : tvWordsK GP xw yw TW 38 1 = true := tvXYS 38 (by quickRfl)
theorem tv39 : tvWordsK GP xw yw TW 39 1 = true := tvXYS 39 (by quickRfl)
theorem tv40 : tvWordsK GP xw yw TW 40 1 = true := tvXYS 40 (by quickRfl)
theorem tv41 : tvWordsK GP xw yw TW 41 1 = true := tvXYS 41 (by quickRfl)
theorem tv42 : tvWordsK GP xw yw TW 42 1 = true := tvXYS 42 (by quickRfl)
theorem tv43 : tvWordsK GP xw yw TW 43 1 = true := tvXYS 43 (by quickRfl)
theorem tv44 : tvWordsK GP xw yw TW 44 1 = true := tvXYS 44 (by quickRfl)
theorem tv45 : tvWordsK GP xw yw TW 45 1 = true := tvXYS 45 (by quickRfl)
theorem genAll : ∀ k < 46, gensOK CFSG.KD.Misc.Unitary.UL UP GP k 1 = true := by
  intro k hk
  interval_cases k
  exacts [gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7, gen8, gen9, gen10, gen11, gen12, gen13, gen14, gen15, gen16, gen17, gen18, gen19, gen20, gen21, gen22, gen23, gen24, gen25, gen26, gen27, gen28, gen29, gen30, gen31, gen32, gen33, gen34, gen35, gen36, gen37, gen38, gen39, gen40, gen41, gen42, gen43, gen44, gen45]
theorem tvAll : ∀ k < 46, tvWordsK GP xw yw TW k 1 = true := by
  intro k hk
  interval_cases k
  exacts [tv0, tv1, tv2, tv3, tv4, tv5, tv6, tv7, tv8, tv9, tv10, tv11, tv12, tv13, tv14, tv15, tv16, tv17, tv18, tv19, tv20, tv21, tv22, tv23, tv24, tv25, tv26, tv27, tv28, tv29, tv30, tv31, tv32, tv33, tv34, tv35, tv36, tv37, tv38, tv39, tv40, tv41, tv42, tv43, tv44, tv45]

end CFSG.KD.Misc.T46

end
