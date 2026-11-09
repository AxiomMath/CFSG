
module

public import Certificates.Data.Kernel.PermCent.L34ModelWalk
public import Certificates.Data.Kernel.PermCent.KGrpC
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.PermCent.KGrpConjSound
import CFSG.GH74.KGroups.L34AutInputs
import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Data.Kernel.PermCent.L34CodesEval
public import Certificates.Data.Kernel.PermCent.L34ModelLspP
public import Certificates.Data.Kernel.PermCent.L34OrbW
public import CFSG.Certificates.Kernel.PermCent.CodeTabSound
public import Certificates.Kernel.PermCent.KG5122
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.PermCent.L34OrbA

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34Mod

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates CFSG.Sporadic.Schreier

theorem kS : sC.length = 64 := by decide +kernel

theorem kFix : fixC 20 28 sC gS = true := by decide +kernel

theorem kLen : levA.length = 6 := by decide +kernel

#kc_eval CFSG.Certificates.Kernel.PkCV.L34Mod levE CFSG.Certificates.Kernel.PkCV.L34Ev.levQA

theorem kLevE : (levA.map (·.map Subtype.val) == levE.lev) = true := by decide +kernel

theorem levA_val : levA.map (·.map Subtype.val) = levE.lev := eq_of_beq kLevE

theorem canon_levE : ∀ T ∈ levE.lev, ∀ c ∈ T, Canon 42 c := by
  intro T hT c hc
  rw [← levA_val] at hT
  obtain ⟨T', -, rfl⟩ := List.mem_map.1 hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hc
  exact t.2

@[expose] noncomputable def ofCodes : (L : List Nat) → (∀ c ∈ L, Canon 42 c) → List (CV 42) :=
  List.rec (motive := fun L => (∀ c ∈ L, Canon 42 c) → List (CV 42)) (fun _ => [])
    (fun c _ ih h => ⟨c, h c (List.mem_cons.2 (Or.inl rfl))⟩ ::
      ih fun x hx => h x (List.mem_cons.2 (Or.inr hx)))

@[expose] noncomputable def ofCodes2 :
    (L : List (List Nat)) → (∀ T ∈ L, ∀ c ∈ T, Canon 42 c) → List (List (CV 42)) :=
  List.rec (motive := fun L => (∀ T ∈ L, ∀ c ∈ T, Canon 42 c) → List (List (CV 42)))
    (fun _ => [])
    (fun T _ ih h => ofCodes T (h T (List.mem_cons.2 (Or.inl rfl))) ::
      ih fun x hx => h x (List.mem_cons.2 (Or.inr hx)))

theorem ofCodes_val : ∀ (L : List Nat) (h : ∀ c ∈ L, Canon 42 c),
    (ofCodes L h).map Subtype.val = L
  | [], _ => rfl
  | c :: L, h => by
    change c :: (ofCodes L _).map Subtype.val = c :: L
    rw [ofCodes_val]

theorem ofCodes2_val : ∀ (L : List (List Nat)) (h : ∀ T ∈ L, ∀ c ∈ T, Canon 42 c),
    (ofCodes2 L h).map (·.map Subtype.val) = L
  | [], _ => rfl
  | T :: L, h => by
    change (ofCodes T _).map Subtype.val :: (ofCodes2 L _).map (·.map Subtype.val) = T :: L
    rw [ofCodes_val, ofCodes2_val]

@[expose] noncomputable def levL : List (List (CV 42)) := ofCodes2 levE.lev canon_levE

theorem levA_eq : levA = levL :=
  (List.map_injective_iff.2 (List.map_injective_iff.2 Subtype.val_injective))
    (levA_val.trans (ofCodes2_val levE.lev canon_levE).symm)

theorem kMask : masksC 20 28 (levA.zip mskA) = true := by
  rw [levA_eq]
  decide +kernel

theorem cnt_conj {n : Nat} [Small n] (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (x r : CV n)
    (hx : ∀ y ∈ elemsC Q, x * y * x⁻¹ ∈ elemsC Q) :
    ((elemsC Q).filter fun h => eq22C h (x * r * x⁻¹) (x * r * x⁻¹) h).length =
      ((elemsC Q).filter fun h => eq22C h r r h).length := by
  set L := elemsC Q with hL
  have hnd : L.Nodup := nodup_elemsC Q hQ
  have hnd' : (L.map fun z => x * z * x⁻¹).Nodup := hnd.map fun a b h => by simpa using h
  have hp : (L.map fun z => x * z * x⁻¹).Perm L :=
    (hnd'.subperm fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hx z hz).perm_of_length_le (by rw [List.length_map])
  have hφ : ∀ z, eq22C (x * z * x⁻¹) (x * r * x⁻¹) (x * r * x⁻¹) (x * z * x⁻¹) =
      eq22C z r r z := by
    intro z
    rw [eq22C_eq, eq22C_eq, decide_eq_decide]
    constructor
    · intro h
      calc z * r = x⁻¹ * ((x * z * x⁻¹) * (x * r * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * r * x⁻¹) * (x * z * x⁻¹)) * x := by rw [h]
        _ = r * z := by group
    · intro h
      calc (x * z * x⁻¹) * (x * r * x⁻¹) = x * (z * r) * x⁻¹ := by group
        _ = x * (r * z) * x⁻¹ := by rw [h]
        _ = (x * r * x⁻¹) * (x * z * x⁻¹) := by group
  rw [← (hp.filter fun h => eq22C h (x * r * x⁻¹) (x * r * x⁻¹) h).length_eq, List.filter_map,
    List.length_map]
  congr 1
  apply List.filter_congr
  intro z _
  exact hφ z

@[expose] noncomputable def wordA (w : List Nat) : CV 42 := w.foldr (fun j x => gA.getD j 1 * x) 1

@[expose] noncomputable def rep (i : Nat) : CV 42 :=
  wordA ([[2, 3, 4, 2, 4], [4, 2, 3, 2, 0]].getD i [])

@[expose] def lsp : List (Nat × Nat × List Nat) := [
  (5329046103897471925010054189686265200566452170814611919048896296098359785,
    1, [2, 3, 2, 4, 4]),
  (10825052598436442407910277940992275319604295173154726305299799721950160361,
    1, [4, 3, 2, 4]),
  (26950052924858837667919944644793918993545485850444653867445770934392547433,
    1, [4, 3, 3, 0, 1]),
  (226185387934856422389914818196400149073238499568477043251561813702990273000,
    1, [1, 2, 2, 4]),
  (242502422697464185407583369922976338284667274284251814361438591685534849179,
    1, [3, 2, 1, 2, 0]),
  (245819932386940362195652900886136716985306095892430874212055976028981860453,
    1, [1, 0, 3, 2]),
  (342796053197224736395441381321242433271072290293015821874614673923184691686,
    1, [1, 1, 0, 3, 1]),
  (362428920023917129221933699210635769684330073761957667187106177985869617307,
    1, [3, 1, 3, 4, 1]),
  (371484380771917884997571711520563992893683312948083730404910872824679605732,
    1, []),
  (461484455537581443706277838014431157681726593786545963823561390950120294555,
    1, [2, 0, 1, 0, 2]),
  (477388308792808591122561335454721185534201360971922794464858691727917163999,
    1, [1, 0, 2, 4]),
  (486216398723024055601791535763205068468587475012628945635564533533965178966,
    1, [3, 1, 0]),
  (571138100571002264503403300607101655698264496170010614038137106992111650973,
    1, [4, 4, 4, 3]),
  (576213114018739985931698307211715731226844026328554631974275763707971471462,
    1, [2, 0, 3]),
  (595458972285583455873846422962358780822310381309932787063441535803564853728,
    1, [4, 4, 3, 0, 1]),
  (684108432495552438470559947763381946137517511875570948735227141991887386085,
    1, [3, 1, 4, 0]),
  (705304617956526538698196931027052045806695609782778554900510394726273869978,
    1, [0, 1, 3, 1, 3]),
  (708843496610376038209419983575526219449747213736346560687549980893007706208,
    1, [0, 4, 1, 4, 1]),
  (802371593994406771510699039136363127014034589103742946746715268494436227221,
    1, [1, 3, 2, 4]),
  (818086115653240154577934375475384828572650686216666299839983988485342980575,
    1, [1, 2, 3, 2, 0]),
  (822027411950637240570228171310891496933612750021378119676969697616249869792,
    1, [2, 1, 4, 0, 4]),
  (1024998691896568420675558637019538608335021231784838011480955081321003219101,
    1, [0, 3, 4, 4, 2]),
  (1026573086330259572832024218588492117362670206720199083383203216117075151333,
    1, [3, 4, 3, 1]),
  (1051718379417623298635746566081805799694904545875180888497709277487627851222,
    1, [4, 1, 0, 3]),
  (1143593576690289784853561566033561468869327589219059093303618486466462214298,
    1, [1, 4, 3, 4]),
  (1153980307494003615357858975777998612463750998609656810500538015441642448991,
    1, [3, 1, 0, 1, 3]),
  (1162619061825963919137160093352685342017498302383630764191900869483857045988,
    1, [0, 3, 2, 2, 4]),
  (1244196034022304726294420784153303606184175439286152768970465879600409450600,
    1, [1, 1, 1, 2]),
  (1260093356335589980084308694075310327372080828182205948418379125169756165606,
    1, [1, 3, 4]),
  (1261863990745931264316669026575887110188798442700499332884184124703387306133,
    1, [1, 0, 4, 2, 0]),
  (1473884850786686648320160406726991048888657323532728671357082453478301665437,
    1, [1, 3, 0, 3]),
  (1482723864656195539872228014487339595351707600966973929215930931428797797849,
    1, [3, 3, 3, 0, 4]),
  (1502152185314578547867685519779620673920810033344000483437266405669804599396,
    1, [3, 2, 3, 1, 1]),
  (1583542318347121797110398110727502285103397047658832217658147838332566615528,
    1, [3, 0, 1, 2]),
  (1600798940424840590342467476469406046365549129915381248656248640960735103449,
    1, [0, 2, 3, 2, 0]),
  (1602752041439218471400863286225801298891663708210363612835528378754650499226,
    1, [1, 3, 4, 0]),
  (1703469319489423220386638858102141061255261273042734002756319486672785520729,
    1, [1, 1, 4, 1, 2, 0]),
  (1721356387808451221121646832513709995410433817629970767616058934014535415957,
    1, [4, 4, 0, 1]),
  (1729773999071077673408102702457413936229494838106310344317887524599047797206,
    1, [0, 4, 4, 2]),
  (1938261008090098366968289511403777586016764599739090166270427771186245163480,
    1, [3, 3, 2, 3]),
  (1940441602189826650318030860328239689157594020193640568577321427746096564312,
    1, [0, 3, 2, 4]),
  (1941991867681495657664567692111477736262776879276168049423548074316399990232,
    1, [1, 2, 0, 1, 0]),
  (2042699965879352023412644272456055490361909117721202464352356207072839579102,
    1, [4, 2, 0, 4]),
  (2044688552713285583937526767481896147577741909377416975181622751958578628702,
    1, [3, 2, 3, 3, 4]),
  (2060175699552472279357473370186944681774610741150641696296478211939780106718,
    1, [0, 2, 0, 2, 1, 0]),
  (2152464100014431973851885134348398866665462254380762803188059603489216170083,
    1, [1, 4, 2, 3]),
  (2160888105944540440465228657401753096742862782788241525591721923199349946851,
    1, [3, 0, 2, 1]),
  (2171677254391801857450596810433222735055196652029983056838587575138703234531,
    1, [0, 4, 4, 1]),
  (2446409573645929137062515234868788395452171661196605694528020250747885622016,
    0, [1, 1, 3, 4]),
  (2446409614505173908868498619298022156872262045837154577892348455369061503759,
    0, [4, 0, 1, 0]),
  (2446409653475915913319329366539810566317375927592070491189908923406099436302,
    0, []),
  (2530770994530780618632337079992832721277502008800573047301272825802662633554,
    0, [2, 4, 3, 1]),
  (2541681360262727836018978485226381229462222937335834471130899431910382260301,
    0, [4, 2, 1, 1, 1]),
  (2550650611644155190622356316111359475758585290274633748232643927904302661698,
    0, [3, 1, 0, 3, 0]),
  (2758692965278744592282074118143138736768730003446351410810161818898925371456,
    0, [1, 3, 3]),
  (2760908007134109805109795180602923517473647447117076933167092853002824659466,
    0, [2, 1, 4, 1]),
  (2762509636063512171313695205181152749702389488645976032602129674712282321408,
    0, [0, 3, 4, 0, 2]),
  (2771504230729858321487401987227404812752552273657330919335525397200520406016,
    0, [2, 2, 4, 1]),
  (2780341181109920445234556014328613953212406868173957348416558079242609643593,
    0, [0, 2, 0, 2]),
  (2785502305364270047028859412315304267274981092521121976939579070248053920779,
    0, [4, 2, 1, 0]),
  (2866471492106511441948004816789843353797885070851028661445619213119552008275,
    0, [2, 3, 4, 1]),
  (2891651577206002252927924837312599711319204995314103081453466930359023710272,
    0, [4, 3, 4, 1]),
  (2898555518904349898031681181405568898995963422449063132592160558546075013201,
    0, [2, 0, 4, 2]),
  (2979859352706738116382638825668314676896722199176332338008950256211494445837,
    0, [4, 4, 0, 2]),
  (2997665514538692941580137088880408203078803993427145579551636112136143905543,
    0, [0, 1, 1]),
  (3011629466085004862321700812631087937709788715716818690786559728572138005266,
    0, [2, 4, 4, 3, 1]),
  (3093072661132007197183458265326325784486571038547002516714220470191948882707,
    0, [4, 4, 3, 1]),
  (3117645857635107955194841263515276763711959891273843558810629181849843049216,
    0, [1, 4, 1, 0]),
  (3124436789960549688355596459493375876929139225988306504137711736922875650833,
    0, [1, 2, 2, 0]),
  (3336458863819260425737768551551096204843338509792916518099061363882504532736,
    0, [1, 2]),
  (3343962356606501115091788666608923434578674885907176084669816676051049853701,
    0, [1, 3, 2, 4]),
  (3350894297249826451633504940269054142564036085541976988354760007525352665862,
    0, [2, 3, 3, 4, 0]),
  (3437609962092975052788425031923482547242714170777398420970582007429007671362,
    0, [0, 4]),
  (3439239629051100426914919650498503167088440577850221636225976464240278282765,
    0, [0, 1, 3, 2]),
  (3444672637311378282752714138027901467765921874009395669977947399514807374354,
    0, [3, 1]),
  (3448043703987655302621746257467721541102604983897686612935204755310082826322,
    0, [4, 0]),
  (3457042220062472623080228475946344030721790485911938343783235516087511852039,
    0, [3, 4]),
  (3463666999715940961582335499698351422222848296789901013778497802795668517906,
    0, [1, 3, 1, 4]),
  (3545387147559985900791609122343058861627662658328700200253886041712289128515,
    0, [4, 3, 3]),
  (3562887893637948998530250268121247863369056619027311131590332127144156602432,
    0, [3, 4, 0, 1, 0]),
  (3577047655267129831981458798380094296574683256078395913299618415488214507588,
    0, [3, 2]),
  (3662000010255285474922399440718027268690511429497064289941264250406712938577,
    0, [0, 4, 2]),
  (3672432856386371044709996558395699416240423483129334060392465890783833944147,
    0, [3, 4, 2, 4]),
  (3680993999778642463294417987537351530752484536649548134079425648631210590272,
    0, [3, 4, 1, 0]),
  (3997696558754731227354703082233499692405353218621863158657488460513445483530,
    0, [0, 1, 3]),
  (4006532592918134615454526205109370477769737647813573916730612639999738835465,
    0, [2, 4, 4]),
  (4009627513705084201316146377590968746123867344299293518605976982866829795840,
    0, [4, 1, 0]),
  (4013596064823766943641397694735935302910160816075382622242077160436776054848,
    0, [4, 1, 4, 1, 2]),
  (4024065206602640540020317243497411574120919563164032574173928011756302299211,
    0, [3, 2, 2, 4, 0]),
  (4029333738968295254855542785243856261975904643449863538492485184048655037440,
    0, [3, 0, 2, 0]),
  (4114147561840445539930935314337308683202096174967923472299773227155114172480,
    0, [1, 3, 1]),
  (4124908759335889219282974402357342739426746784772158910597137437940078616643,
    0, [1, 2, 4]),
  (4133610142812365073365656357678484319025283020618469787976128376970431701060,
    0, [4, 3, 1, 0]),
  (4241520260700053249430538288109478036490950674150776224675044841461844873285,
    0, [3, 1, 4, 3, 2]),
  (4248454359416023418002516646755019246063237655879265035257686915426276646982,
    0, [1, 2, 0]),
  (4255215913176126375356501336120187053204860933766400549466885754298240352320,
    0, [4, 1, 1, 1, 0]),
  (4368740466405571889342547518977334619061508974901042295313402970223963537474,
    0, [1, 4, 4, 3]),
  (4368740507908745371527575348593846950229064206447554819124001855348478373959,
    0, [3, 3, 4, 3]),
  (4368740542039822102436498233628346213660355239878805481384174061010842869842,
    0, [2, 0, 1, 1]),
  (4596662450630218168626278239217517716391709099864526538659449115925366517839,
    0, [2, 3, 3]),
  (4596662491718724508738574391490463259470868724865145106330181486575633342542,
    0, [2, 4, 2, 2]),
  (4596662532691809207719112797529547094094537930795997371248890519169777807424,
    0, [3, 3, 4, 1, 0]),
  (4674403721712740727242607827538297227994599538524119855329051587112782275086,
    0, [1, 4, 0]),
  (4674403762450518332816357873089899027738660414917961494727527989662247580160,
    0, [3, 3, 0, 2]),
  (4674403802689407966351720450973573774989870187333950978442777673180922585615,
    0, [0, 3, 4, 3, 0]),
  (4676001018726080055906408120349533269550291561509147527389830885264368083987,
    0, [1, 0, 2]),
  (4681330467196793786105558269272356918106823313364906417373214930591919382596,
    0, [4, 4, 3, 0]),
  (4682793306109715172451917155484047155019721666652203421061067780402522673683,
    0, [3, 3, 4, 0]),
  (4684861242367461720042547285495740418200273715551813133907296165253938160139,
    0, [2, 0, 1, 0]),
  (4688372512571125006535221429332157989075320787643934891765256806614671565329,
    0, [1, 1, 4, 4, 0]),
  (4691629598911621887573965125152564018924499414729033891658556021978003984465,
    0, [1, 1, 1]),
  (4693696287552749719021712759685346760505200831627074558095673836149676450822,
    0, [3, 3, 1, 4, 2]),
  (4700459568024705330695047887850111997329417025864977716922917960479736910848,
    0, [0, 4, 4]),
  (4702500832698813717520593318677112086528387084155229636858120612865767383104,
    0, [0, 1, 4, 2]),
  (4704440964188636268343740857507985351325095904524774749741018628461822550090,
    0, [2, 4, 4, 0]),
  (4704441032230507263459747079234491286984050110128576861533315152941645045827,
    0, [1, 0, 3]),
  (4704441059830576418622204219069012183851137039857956818399846696638849249363,
    0, [1, 2, 4, 2]),
  (4707966489148567852438557234160634774354904865566785660542515600512892040209,
    0, [0, 4, 1, 3]),
  (4707966497353032220239941551456928042250173948545066447155974416037881586697,
    0, [4, 1, 4, 1]),
  (4707966510429599513418569809339985260005595875817024214137118141378131207173,
    0, [1, 0, 3, 2])]

theorem kConj : (lsp.all fun e =>
    Nat.blt e.2.1 2 && Nat.beq (wordA e.2.2 * rep e.2.1 * (wordA e.2.2)⁻¹).1 e.1) = true := by
  decide +kernel

@[expose] noncomputable def gPM : List (CV 42) := [cOf PA, cOf PB]

theorem hgPM : QP.originalSubgroup = Subgroup.closure {σ | σ ∈ gPM.map ev} := by
  rw [QP, certificate_originalSubgroup]
  simp only [gPM, List.map_cons, List.map_nil, ev_cOf]

#kmisc_packarrs CFSG.Certificates.Kernel.PkCV.L34Mod.XO0 CFSG.Certificates.Kernel.PkCV.L34Orb.orbA0 6
#kmisc_packarrs CFSG.Certificates.Kernel.PkCV.L34Mod.XO1 CFSG.Certificates.Kernel.PkCV.L34Orb.orbA1 6

theorem kOrb : orbTabOK gPM (rep 0) L34Orb.orbW0 XO0 L34Orb.orbR0 = true ∧
    orbTabOK gPM (rep 1) L34Orb.orbW1 XO1 L34Orb.orbR1 = true := by
  decide +kernel

theorem kCnt0 (hP : ValidSchreier QP) :
    ((elemsC QP).filter fun h => eq22C h (rep 0) (rep 0) h).length = 168 := by
  have h := count_mul_orbit QP hP gPM hgPM (rep 0) L34Orb.orbW0 XO0 L34Orb.orbR0 kOrb.1
  rw [CFSG.GH74.KGroups.card_group QP hP, PkEnum.orderCertificate_eq_orderV, KGrp.K5122.kQP] at h
  have hl : L34Orb.orbW0.length = 120 := rfl
  rw [hl] at h
  omega

theorem kCnt1 (hP : ValidSchreier QP) :
    ((elemsC QP).filter fun h => eq22C h (rep 1) (rep 1) h).length = 60 := by
  have h := count_mul_orbit QP hP gPM hgPM (rep 1) L34Orb.orbW1 XO1 L34Orb.orbR1 kOrb.2
  rw [CFSG.GH74.KGroups.card_group QP hP, PkEnum.orderCertificate_eq_orderV, KGrp.K5122.kQP] at h
  have hl : L34Orb.orbW1.length = 336 := rfl
  rw [hl] at h
  omega

theorem kNP : normC QP (QA.original.toList.map cOf) (cOf PA) (cOf PB) = true ∧
    (lspP.all fun e => Nat.beq (wordA e.2).1 e.1 && siftC QP (wordA e.2) 0) = true := by
  decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf PA) (cOf PB) = true := kNP.1

theorem wordA_mem (w : List Nat) : ev (wordA w) ∈ QA.originalSubgroup := by
  induction w with
  | nil => rw [wordA, List.foldr_nil, ev_one]; exact one_mem _
  | cons j w ih =>
    change ev (gA.getD j 1 * wordA w) ∈ _
    rw [ev_mul]
    refine mul_mem ?_ ih
    rw [List.getD_eq_getElem?_getD]
    cases h : gA[j]? with
    | none => rw [Option.getD_none, ev_one]; exact one_mem _
    | some a =>
      rw [Option.getD_some]
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? h)
      rw [ev_cOf, RawSchreierDatum.originalSubgroup]
      exact Subgroup.subset_closure hσ

theorem wordA_conj (hP : ValidSchreier QP) (w : List Nat) (y : CV 42) (hy : y ∈ elemsC QP) :
    wordA w * y * (wordA w)⁻¹ ∈ elemsC QP := by
  have hN := le_normalizer_of_normC QP QA hP (cOf PA) (cOf PB)
    (by rw [ev_cOf, ev_cOf]; rfl) kNorm (wordA_mem w)
  rw [mem_elemsC QP hP] at hy ⊢
  rw [ev_mul, ev_mul, ev_inv]
  exact (Subgroup.mem_normalizer_iff.1 hN _).1 hy

@[expose] noncomputable def bodyE (m c : CV 42 → Bool) (g : CV 42) : Bool :=
  (!(gS.all fun s => eq22C g s s g) || decide (g ∈ sC)) &&
    (!powOneC g 2 || m g ||
      !(gS.all fun s => decide (g * s * g⁻¹ ∈ sC)) ||
      c g ||
      gA.all fun a => m (a * g * a⁻¹ * g⁻¹))

theorem bodyE_mono (m₁ m₂ c₁ c₂ : CV 42 → Bool) (g : CV 42) (hm : ∀ x, m₁ x = true → m₂ x = true)
    (hc : c₁ g = true → c₂ g = true) (h : bodyE m₁ c₁ g = true) : bodyE m₂ c₂ g = true := by
  unfold bodyE at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  simp only [Bool.or_eq_true] at h ⊢
  rcases h.2 with (((h1 | h2) | h3) | h4) | h5
  · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (hm g h2))))
  · exact Or.inl (Or.inl (Or.inr h3))
  · exact Or.inl (Or.inr (hc h4))
  · exact Or.inr (List.all_eq_true.2 fun a ha => hm _ (List.all_eq_true.1 h5 a ha))

@[expose] noncomputable def bodyD (c : CV 42 → Bool) (g : CV 42) : Bool :=
  bodyE (fun x => siftC QP x 0) c g

theorem bodyD_mono (c₁ c₂ : CV 42 → Bool) (g : CV 42) (hc : c₁ g = true → c₂ g = true)
    (h : bodyD c₁ g = true) : bodyD c₂ g = true :=
  bodyE_mono _ _ c₁ c₂ g (fun _ hx => hx) hc h

@[expose] noncomputable def bodyY : CV 42 → Bool := bodyD fun g => lsp.any fun e => Nat.beq g.1 e.1

theorem bodyC_of_bodyY (hP : ValidSchreier QP) (g : CV 42) (h : bodyY g = true) :
    bodyC (elemsC QP) sC gS g = true := by
  refine bodyD_mono _ (fun g => !decide (9 ∣ ((elemsC QP).filter fun h => eq22C h g g h).length))
    g (fun hl => ?_) h
  obtain ⟨e, he, hb⟩ := List.any_eq_true.1 hl
  have hk := List.all_eq_true.1 kConj e he
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hk
  rw [Nat.beq_eq] at hb
  have hg : g = wordA e.2.2 * rep e.2.1 * (wordA e.2.2)⁻¹ := Subtype.ext (hb.trans hk.2.symm)
  rw [hg, cnt_conj QP hP _ _ (wordA_conj hP e.2.2)]
  have hi := hk.1
  obtain ⟨_, i, _⟩ := e
  interval_cases i
  · rw [kCnt0 hP]; decide
  · rw [kCnt1 hP]; decide

@[expose] noncomputable def inPL (x : CV 42) : Bool := lspP.any fun e => Nat.beq x.1 e.1

@[expose] noncomputable def bodyZ : CV 42 → Bool :=
  bodyE inPL fun g => lsp.any fun e => Nat.beq g.1 e.1

theorem bodyY_of_bodyZ (g : CV 42) (h : bodyZ g = true) : bodyY g = true := by
  refine bodyE_mono inPL (fun x => siftC QP x 0) _ _ g (fun x hx => ?_) id h
  obtain ⟨e, he, hb⟩ := List.any_eq_true.1 hx
  have hk := List.all_eq_true.1 kNP.2 e he
  rw [Bool.and_eq_true, Nat.beq_eq] at hk
  rw [Nat.beq_eq] at hb
  have hx' : x = wordA e.2 := Subtype.ext (hb.trans hk.1.symm)
  rw [hx']
  exact hk.2

noncomputable def kWalkB (j : Nat) : Bool :=
  walkC bodyZ
    ((((levL.zip mskA).head!.1.drop (j * 6)).take 6, (levL.zip mskA).head!.2) ::
      (levL.zip mskA).tail) 1 20 28

#kc_each kWalkB 0 7

theorem walkC_of_blocks {n : Nat} [Small n] (body : CV n → Bool) (L : List (List (CV n) × Nat))
    (p : CV n) (a b c m : Nat) (hne : L ≠ []) (hlen : L.head!.1.length ≤ m * c)
    (h : ∀ j < m,
      walkC body (((L.head!.1.drop (j * c)).take c, L.head!.2) :: L.tail) p a b = true) :
    walkC body L p a b = true := by
  obtain _ | ⟨⟨T, M⟩, tl⟩ := L
  · exact absurd rfl hne
  · rw [walkC_cons]
    refine PkEnum.all_of_chunks T _ c m hlen fun j hj => ?_
    have hj' := h j hj
    rw [walkC_cons] at hj'
    exact hj'

theorem kWalk : walkC bodyZ (levA.zip mskA) 1 20 28 = true := by
  rw [levA_eq]
  refine walkC_of_blocks _ _ 1 20 28 6 7 ?_ (by decide +kernel) fun j hj => ?_
  · rw [← List.length_pos_iff, List.length_zip, ← levA_eq, kLen]
    decide
  · interval_cases j
    exacts [kWalkB0, kWalkB1, kWalkB2, kWalkB3, kWalkB4, kWalkB5, kWalkB6]

theorem kScan (hP : ValidSchreier QP) : modelC (elemsC QA) (elemsC QP) sC gS = true := by
  rw [modelC_eq, elemsC_QA, List.all_eq_true]
  intro g hg
  cases hn : (gS.all fun s => decide (g * s * g⁻¹ ∈ sC))
  · exact body_of_not _ _ _ g (fixC_sub kFix) hn
  · have hz : (levA.zip mskA).map Prod.fst = levA := List.map_fst_zip (by rw [kLen]; rfl)
    have hg' : g ∈ productsC ((levA.zip mskA).map Prod.fst) := by
      rw [hz]
      exact hg
    have h := walkC_sound bodyZ (20 : Fin 42) 28 (levA.zip mskA) 1 20 28
      kMask kWalk (by rw [ev_one, inv_one]; rfl) (by rw [ev_one, inv_one]; rfl) g hg'
      (by rw [one_mul]; exact good_of_nrm kFix g hn 20 (Or.inl rfl))
      (by rw [one_mul]; exact good_of_nrm kFix g hn 28 (Or.inr rfl))
    rw [one_mul] at h
    exact bodyC_of_bodyY hP g (bodyY_of_bodyZ g h)

end CFSG.Certificates.Kernel.PkCV.L34Mod

end
