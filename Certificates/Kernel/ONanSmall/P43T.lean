module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import Certificates.Data.Kernel.ONanSmall.P43Gen
public import Certificates.Data.P43Twin
public import Certificates.Kernel.ONanSmall.Data.P43T
import CFSG.Certificates.Kernel.ONanSmall.CVGlue

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.P43T

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.CatFactsSmall CFSG.KD.ONS.P43T Certificates.P43Gen

@[expose] noncomputable def el0 (d : List Nat) : CV 45 := (genC PSp43.QP45 d).getD 1

@[expose] noncomputable def elA (d : List Nat) : CV 45 := (genC PSp43.QA45 d).getD 1

@[expose, reducible] noncomputable def reps0 : List (CV 45) :=
  [cOf (Certificates.P43Twin.tA ()), cOf (Certificates.P43Twin.tB ())]

@[expose, reducible] noncomputable def repsA : List (CV 45) :=
  [cOf (Certificates.P43Twin.tA ()), cOf (Certificates.P43Twin.tB ()),
    cOf (Certificates.P43Twin.t36 ()), cOf (Certificates.P43Twin.t540 ())]

@[expose, reducible] noncomputable def Q1 : List (CV 45) :=
  q8B (cOf (Certificates.P43Twin.tA ())) (cOf (Certificates.P43Twin.a1 ()))
    (cOf (Certificates.P43Twin.b1 ()))

@[expose, reducible] noncomputable def Q2 : List (CV 45) :=
  q8B (cOf (Certificates.P43Twin.tA ())) (cOf (Certificates.P43Twin.a2 ()))
    (cOf (Certificates.P43Twin.b2 ()))

@[expose] noncomputable def cents0 : List (List (CV 45)) := C0.map (List.map el0)

@[expose] noncomputable def centsA : List (List (CV 45)) := CA.map (List.map elA)

@[expose] def tsVP45 : List (List Nat) :=
  [[1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 369320570347332080866071694897057006364230807052024500897345987209471738623205414, 816120455481024857293957581265330395822387683936143635871749226293695711084144385, 279465914481242996847961921255264854439658123210314094181979231010650546859827242, 938071776634831055918545596676987008145295812152895305917130808489655037995354502, 583313754640594417160649343860178579614093371152808532301385348525893540271382531, 225680495881383400272282986093277098510442892549065228755714002790300779809730593, 195632446929387998254355364770605370546932437113886266854663045000414748991926301, 1175351740799080442301189678207165673792060843255065238055876723023383570196467714, 257204893971074651827281470107905913859980508372667653891650311949390641532633116, 405463307010353698488964193350856017533442323692311308595499792104470736243331091, 1281794125427929619051398560287136431758034844941418870829056480661243567401402912, 1112599946155198787393636206432337140398640268809672774542884049524138821737878028, 257677478575478495530225279454612300442414951804507451178276778634801861962000792, 135825840015294316251762805385097009101866793590868790273997764157468362492219423, 108556801204993871206927335531093150398523411275213896352460868962006853742088219, 315608651144264614625120471814255474970916449177688863682516263513702854241890321, 1110320858268742953275305803790505056067951019273207664354661055074707204135817418, 391019311555219923292261583376727733546094866832314391350614000334784547509389991, 1228023537754403890110439326211994588962528622908721658241500505743150987298539597, 1259481903468783614090152491200074032981596077873190807520579676694862435944056590, 695473895613943497512920732411852204502083590839276516341542035387849599722572178, 537959426689839020013143953508230830183026107050720341588328676522674936688308261, 576439267207851481612264152456290739571420328931901953025118394209689154824224777, 401228531527143183091526202847001746495757837366794439419580393798722373830205544, 549111880205725727116810552467552429123771800232342677666512648445668199150706699, 428114007247323777394799817048227134316477482658605407088706503039549380983951403, 418035282602352810966279644413531126849135403986177099429481671751758128122765334, 832932542216239127042680398544273570286714519479258721611287735530875297484425641, 784379118830235266689545092450737398065268718368814392366269456193523486961549406, 250838588860174024706476934162083963528358951597060201187315120208618048320262167, 310182170865768658990090678578005814275516086109425821275440185225546195144036360, 160983932994084940427296474761433778712800023103490153557767280011128364382122005, 1026890974415995300532813861797282980117306116170745276650446452958005973799547460, 876375504688232059022603751467085510157502734745886721599031854550490553310655109, 968980333956130974546477214478739323234307532298705019600448752520484613079053063, 985444303798209172128545193530630904916473039406634738151165935248009999940915820, 839367360869808343885670717549495002334579337665408813556781856214071355850662105, 839366255938182729833067429817757378280108098490368616688411269918660520413919908, 369772606689916916299151100445722290666332501930119453764296983143606727627298896, 401230967105049523284506081724719352361917860765628281733904620984105849308899092, 244788617542411526627726543320611380147863058477643151538593130254070215757292762, 226150903038350674492319299632255540572683065668880410117267967812943968935727202, 42833500366436533258754785992038742334996160245243057548965394368181430829236623, 32922570074039849969361236691481123733765966151273419249903398095544993197200547],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 1323551936092835221201048465889197193977640368861089134228055773665926500247408768, 605407786571275015735633889759236335485535132901493951329385450297631832010025600, 597300418481319480967246073403902640413318656582244687159288819617934410454950080, 1021296571107951011601449436163909127737397120948374860477624305416648559974533120, 458351599867212498825003641233190490571480874717103927579689694603944893790589696, 606312186030510598116926183849091745629947739982514029793283362354551477766891904, 598718532282914239524897317094148640582779465999023535378233995188688502761730432, 1020377697500422255987027423562200293810774623293388079986949139754961928349943552, 457454437247521417153893394876027899864442329888227455421353660249019653292606016, 728662345071116606815927699927278328638779245784445049685477203446610712135342016, 612399751499793095555568870675187747044234781511815011943423353566428962291046080, 1026892578051384938874032181471285507096155014424773914215168336286263117014971456, 778609912895621981888732037734797885566044284354066852337295348461966440343577408, 1186941462626743854438112752716107175862206637916484059750883195491920184876104000, 713518911793253342513397565401690363466868007151213583266292408589613020177552000, 476803816620779049704168714406410971134026000337467306251034404663107519897199296, 1027796977510620521968589993249381649812200505171423503024493747603328253196571840, 601202280841455836824950696215621579495426710824728020221210994639335734095738176, 1203323442328960911043461933014885494852104523998962744989449296998745729691728448, 463868000433215387286515643411401285873608088610336869914134434911262026280501568, 462948236446878493952581170311393173394354771122968601528934993054603451537048000, 1046075522681691932960200961387627998139646900609875334953728762745131247300031360, 1086149212321758833333821911202952667531198552002429113312097360373833421811767744, 464765163052906468955216071180463083668687966886652621669338594205747434750235136, 729566744530352189199629812605234531695183186274133745344001524819312025795950656, 610525819286605964146278021254711313597760125515734262467410497474036196208392000, 603061738906349795001111827267880970074482430609088348518007447861692935928894912, 1205182900393854869219623063923508504516369289421076792438684899484683078804085440, 462007651796311573590643364986877531999097606928823143452004711169350879530217728, 1187325586743593729158744323177157651213364214270255151395060229269906940572034176, 1081603233979910161863732356330081336737199626224475523473917020099809225431917952],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 902942574704215726095399897035556531118055357220828360640402639955195109371813952, 902942574704215725468559849436512372713305672823258992364072685183662857512558656, 1023374043922254390992448280074158154144856126119333768826473575328765077046960192, 482746987804245472910489973232273122682909771666394254779653738631762881073127488, 482746987804245472752569148631299356293830292416374422302266637327928991167029312, 1324506994726093841926301192204114433523397548215791408206330959600062415539806272, 1085012889411924375403848571615595743289233992392828150691593679041385998248583232, 601809623900376274377973386181216423501193079340832271687162414722007358744567872],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 783879938608084924469995659485639463910692570296370511312628825440072340993220672]]

@[expose] def tsVA45 : List (List Nat) :=
  [[1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 369320570347332080866071694897057006364230807052024500897345987209471738623205414, 816120455481024857293957581265330395822387683936143635871749226293695711084144385, 279465914481242996847961921255264854439658123210314094181979231010650546859827242, 938071776634831055918545596676987008145295812152895305917130808489655037995354502, 375312810965391312048930637911471777649757202557258446478683583852768587803906075, 250839629536485392166538681076136308538467495480821531835022580272076255300997130, 642135227981153747979599919791820780099950053762011273197377697463611679351259143, 284531818385403909195663140327150029883308874836359101082434446775319615006158877, 136362510977457564404683727685414637078369176426398436983931227337721623620964375, 225680495881383400272282986093277098510442892549065228755714002790300779809730593, 257204893971074651827281470107905913859980508372667653891650311949390641532633116, 405463307010353698488964193350856017533442323692311308595499792104470736243331091, 875398534941127596994353952817655882621994428243413626386892536343501336765130754, 814492129225913000097492795562051165407451374903006469347087379017231664775571231, 1135758741693719672065991804171774371400322958851213032668984142986195473718413132, 956040627366445471046481973073971079032664667277670393103533283660792665358813765, 257677478575478495530225279454612300442414951804507451178276778634801861962000792, 160984964838317779962561362440851391065601870895897947892177283107327406718361613, 699568109486896148177622489206846308178638731112822471077937506054423233109192708, 227143503557444967414627684441315931690867728590871775947128455729350709589667861, 167350238104985567809171696466113761935407824530957247178068174478453871914369056, 315608651144264614625120471814255474970916449177688863682516263513702854241890321, 998298144035662666527088961987582828619099722926381883241129108367425375066491523, 102167108237873362160077867018440150530631207234333033854640701601207778209534414, 1225743444503902046621126616859005360918568933980730647225051726586466123025589707, 930096596488701261077595069601109091214262780092499111830446218966815690667235756, 222033045070353599284995218963010354948797763305347405372856353558591900176773157, 429621562437256853746138801179461296791404611676927116589271417711979678132674582, 1305480907063317233148922157624881624996362791384062609850891297207997822267207780, 252081094022349001302922840285682082912308218740526367273907311348477930994577449, 79033145296652218722669784415508621770753020732028180130160453860153207229681707, 245728748780305606942622347008210652138496848378542871298577745372468483130179593, 695473088045814795394639441177677513650255564010627547919397259264054298894159880, 712478478607599674362319995003311280222764294544340821080828166755969122835701844, 134031062632061153248143413675776929596466284260398134389173187761387336275742759, 341619579998964407706876588825839933955069717515491813839238769480763888677511186, 1281793561859367592014905310759650276521844742463989011028345362246741840252457246, 79935039496823892037028944904487923967220165688670832680695397941427137654088153, 278101006499702386644556577213971751105008850999928476442430446171877701363742170, 369772606689916916299151100445722290666332501930119453764296983143606727627298896, 251307321362505447201671839946720200874577673528543375158541665013653600110405736, 46631458495156125901096628774397606214765779108447953435241463045562722337178255, 1254350866514486633424969773919497914745529694880533306640008308966722333358028578, 1308140951411902834986342722360994318004881222242849150722059017883858466383896931],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 1323551936092835221201048465889197193977640368861089134228055773665926500247408768, 447978363850883454476870069949523320468347697968507375721302601384548534367164352, 1319135657171073865825117013233747165552434969734465643201484140754369702905287424, 1309125184170369789061250432073304798896980466473292737387851826296240636069445952, 446567487054434669035523999367900914510270081452527639623570353212642130071517248, 1317305147016362818509163649480647248870418427040227099057182814837649020938666560, 1310499875941088708925664298208096955466263989972241879399313933423818825221296640, 448448882043543093785370010437166665112474666471001526853190686591898231430879936, 775642077339295902816539522197212888669459819742255521522590832381606326261539008, 447038005302294799145830701852668927733309835586325930639396902370626540696156736, 1040826673073544141606996840395872636322347840883881160286920235836805456382997568, 788346285588969173933287151018980293110531526953597158766536544490239466567676800, 450244125843268504623693088224999415322509820512364712546646666541266856047438464, 1316885062979118581493743430323522375850955244918353918864119930750827134571607360, 728662344022233247049483048483066268790270667370489727376354012515178041525170432, 908820265180190343426271082064786607874022813804234518825340956654813392818422208, 491455012212720453621222036458277457760265820898776507196919171631174618014065472, 1009555765981905515658997176265819640500540699077892183128285984201574901376144000, 777045717240999696745118618304489749522026216093530535393033307845183947222036864, 1039415796111493883762715627627311924678743362505044497375861113957405482514977984, 790220217774556059940068073883069641397647827689578133082301591568855883463058112, 448833249046819719182384680251544462934042284745286063889873334143367841690593664, 1317789462438354163874652919405808364723811687287677005676657431268214850734347712, 771863003816407384063528104443927476068432977128180249556773001139312712714930176, 745275489450975532870253404100118288357500796921061720553508609101933122006377600, 450244119079645125484363222471071032091218643665885033693572792242537000295053120, 771414422492761720527301641330094109579121326073490950853564434045663740616902400, 746686366247424318311561812073573240745968332688140369210281941499832136363222400, 448833242338396830844861576638377129198577699436445969050636142568672675762919104, 1203323456574191488525840693283285946547120016336170216440909132984992647467661632, 1205182914639085446699554342995640709729783367600714559368802464528732199119641024],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 904766766555602278478877746400819273629311449916827138567766512658224394595213376, 719918120341072387155978685506509818717665477111777166100351272482191448768782400, 902942574704215726095399897035556531118055357220828360640402639955195109371813952, 904766766555602277852075361553578949708995467860267137950666942002152603517198400, 1023374043922254390992448280074158154144856126119333768826473575328765077046960192, 783879938608084923844342885362229402061451193762851894178254266972431788878864448, 603633815751762826761451235546479166012449172036831049595783143355652086624428096, 784378719534040924048789679956541444891759975000953798025016532246261284480229440, 482746987804245472752569148631299356293830292416374422302266637327928991167029312, 1205899717359441729412730658530775553007852872013284777966367040998893302400950336, 601809623900376274534706937306556093334764250726801352965472156842149727714680896],
  [1324506994726093842395220415202184825539067753363340944416092930018803878078455872, 902942574704215725468559849436512372713305672823258992364072685183662857512558656, 482746987804245472910489973232273122682909771666394254779653738631762881073127488]]

theorem canon_of_vals {n : Nat} {Ts : List (List (CV n))} {N : List (List Nat)}
    (h : Ts.map (List.map Subtype.val) = N) : ∀ l ∈ N, ∀ p ∈ l, Canon n p := by
  subst h
  intro l hl p hp
  obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
  exact c.2

@[expose] def mkTs {n : Nat} (N : List (List Nat)) (h : ∀ l ∈ N, ∀ p ∈ l, Canon n p) :
    List (List (CV n)) :=
  N.pmap (fun l hl => l.pmap Subtype.mk hl) h

theorem pmap_val {n : Nat} (l : List Nat) (h : ∀ p ∈ l, Canon n p) :
    (l.pmap Subtype.mk h).map Subtype.val = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.pmap, List.map_cons, ih]

theorem mkTs_vals {n : Nat} (N : List (List Nat)) (h : ∀ l ∈ N, ∀ p ∈ l, Canon n p) :
    (mkTs N h).map (List.map Subtype.val) = N := by
  induction N with
  | nil => rfl
  | cons l N ih =>
    simp only [mkTs] at ih ⊢
    simp only [List.pmap, List.map_cons, pmap_val, ih]

theorem eq_mkTs {n : Nat} {Ts : List (List (CV n))} {N : List (List Nat)}
    (h : Ts.map (List.map Subtype.val) = N) : Ts = mkTs N (canon_of_vals h) := by
  have hi : Function.Injective (List.map (List.map (Subtype.val (p := Canon n)))) :=
    List.map_injective_iff.2 (List.map_injective_iff.2 Subtype.val_injective)
  exact hi (h.trans (mkTs_vals N _).symm)

theorem tsP_ok : (TsC PSp43.QP45).map (List.map Subtype.val) = tsVP45 := by decide +kernel

theorem tsA_ok : (TsC PSp43.QA45).map (List.map Subtype.val) = tsVA45 := by decide +kernel

@[expose] noncomputable def tsCP : List (List (CV 45)) := mkTs tsVP45 (canon_of_vals tsP_ok)

@[expose] noncomputable def tsCA : List (List (CV 45)) := mkTs tsVA45 (canon_of_vals tsA_ok)

theorem elemsQP_eq : elemsC PSp43.QP45 = productsC tsCP := congrArg productsC (eq_mkTs tsP_ok)

theorem elemsQA_eq : elemsC PSp43.QA45 = productsC tsCA := congrArg productsC (eq_mkTs tsA_ok)

theorem genP0_eq : genC PSp43.QP45 = genP tsCP := funext fun d => congrArg (genP · d) (eq_mkTs tsP_ok)

theorem genPA_eq : genC PSp43.QA45 = genP tsCA := funext fun d => congrArg (genP · d) (eq_mkTs tsA_ok)

theorem cents0_eq : cents0 = C0.map (List.map fun d => (genP tsCP d).getD 1) := by
  unfold cents0 el0
  rw [genP0_eq]

theorem centsA_eq : centsA = CA.map (List.map fun d => (genP tsCA d).getD 1) := by
  unfold centsA elA
  rw [genPA_eq]

theorem one0_mem : (1 : CV 45) ∈ elemsC PSp43.QP45 := by
  rw [elemsQP_eq]
  decide +kernel

theorem oneA_mem : (1 : CV 45) ∈ elemsC PSp43.QA45 := by
  rw [elemsQA_eq]
  decide +kernel

section Blocks

variable {M : Type*} [Group M] {D : Type*}

@[expose] def pickRunS (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) : List M → List M → List (ℕ × D) → Option (List M × List (ℕ × D))
  | reps, [], W => some (reps, W)
  | reps, t :: ts, W =>
    if inv t then
      match W with
      | [] => none
      | (j, d) :: W' =>
        if j == reps.length then
          if L₀.any fun g => reps.any fun r => conj g t r then none
          else pickRunS L₀ inv conj gen (reps ++ [t]) ts W'
        else
          match gen d with
          | some g => if j < reps.length && conj g t (reps.getD j 1) then
              pickRunS L₀ inv conj gen reps ts W' else none
          | none => none
    else pickRunS L₀ inv conj gen reps ts W

theorem pickRun_eq_S (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) : ∀ (reps ts : List M) (W : List (ℕ × D)),
      pickRun L₀ inv conj gen reps ts W = (pickRunS L₀ inv conj gen reps ts W).map Prod.fst
  | reps, [], W => rfl
  | reps, t :: ts, W => by
    simp only [pickRun, pickRunS]
    by_cases hi : inv t = true
    · rw [ite_eq_left hi, ite_eq_left hi]
      cases W with
      | nil => rfl
      | cons e W' =>
        obtain ⟨j, d⟩ := e
        dsimp only
        by_cases hj : (j == reps.length) = true
        · rw [ite_eq_left hj, ite_eq_left hj]
          by_cases ha : (L₀.any fun g => reps.any fun r => conj g t r) = true
          · rw [ite_eq_left ha, ite_eq_left ha]
            rfl
          · rw [ite_eq_right ha, ite_eq_right ha]
            exact pickRun_eq_S L₀ inv conj gen _ ts W'
        · rw [ite_eq_right hj, ite_eq_right hj]
          cases gen d with
          | none => rfl
          | some g =>
            dsimp only
            by_cases hc : (j < reps.length && conj g t (reps.getD j 1)) = true
            · rw [ite_eq_left hc, ite_eq_left hc]
              exact pickRun_eq_S L₀ inv conj gen _ ts W'
            · rw [ite_eq_right hc, ite_eq_right hc]
              rfl
    · rw [ite_eq_right hi, ite_eq_right hi]
      exact pickRun_eq_S L₀ inv conj gen _ ts W

theorem pickRunS_append (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (ys : List M) (W₂ : List (ℕ × D)) :
    ∀ (xs reps : List M) (W₁ : List (ℕ × D)) (r : List M),
      pickRunS L₀ inv conj gen reps xs W₁ = some (r, []) →
      pickRunS L₀ inv conj gen reps (xs ++ ys) (W₁ ++ W₂) = pickRunS L₀ inv conj gen r ys W₂
  | [], reps, W₁, r, h => by
    simp only [pickRunS, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | t :: xs, reps, W₁, r, h => by
    rw [List.cons_append]
    simp only [pickRunS] at h ⊢
    by_cases hi : inv t = true
    · rw [ite_eq_left hi] at h ⊢
      cases W₁ with
      | nil => exact absurd h (by simp)
      | cons e W' =>
        obtain ⟨j, d⟩ := e
        rw [List.cons_append]
        dsimp only at h ⊢
        by_cases hj : (j == reps.length) = true
        · rw [ite_eq_left hj] at h ⊢
          by_cases ha : (L₀.any fun g => reps.any fun r => conj g t r) = true
          · rw [ite_eq_left ha] at h
            exact absurd h (by simp)
          · rw [ite_eq_right ha] at h ⊢
            exact pickRunS_append L₀ inv conj gen ys W₂ xs _ W' r h
        · rw [ite_eq_right hj] at h ⊢
          cases hg : gen d with
          | none =>
            rw [hg] at h
            exact absurd h (by simp)
          | some g =>
            rw [hg] at h
            dsimp only at h ⊢
            by_cases hc : (j < reps.length && conj g t (reps.getD j 1)) = true
            · rw [ite_eq_left hc] at h ⊢
              exact pickRunS_append L₀ inv conj gen ys W₂ xs _ W' r h
            · rw [ite_eq_right hc] at h
              exact absurd h (by simp)
    · rw [ite_eq_right hi] at h ⊢
      exact pickRunS_append L₀ inv conj gen ys W₂ xs _ W₁ r h

theorem pickRunS_flatten (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (reps : List M) :
    ∀ (Bs : List (List M)) (Ws : List (List (ℕ × D))), Bs.length = Ws.length →
      (∀ k, k < Bs.length →
        pickRunS L₀ inv conj gen reps (Bs.getD k []) (Ws.getD k []) = some (reps, [])) →
      pickRunS L₀ inv conj gen reps Bs.flatten Ws.flatten = some (reps, [])
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | B :: Bs, V :: Ws, hl, h => by
    rw [List.flatten_cons, List.flatten_cons,
      pickRunS_append L₀ inv conj gen _ _ B reps V reps (h 0 (by simp))]
    exact pickRunS_flatten L₀ inv conj gen reps Bs Ws (by simpa using hl)
      fun k hk => h (k + 1) (by simp [hk])

@[expose] def cutL {α : Type*} : List ℕ → List α → List (List α)
  | [], l => [l]
  | n :: ns, l => l.take n :: cutL ns (l.drop n)

theorem flatten_cutL {α : Type*} : ∀ (ns : List ℕ) (l : List α), (cutL ns l).flatten = l
  | [], l => by simp [cutL]
  | n :: ns, l => by rw [cutL, List.flatten_cons, flatten_cutL ns, List.take_append_drop]

theorem filter_flatten_of {α β : Type*} (q : α → Bool) (f : β → α) :
    ∀ (Bs : List (List α)) (Cs : List (List β)), Bs.length = Cs.length →
      (∀ k, k < Bs.length → (Bs.getD k []).filter q = (Cs.getD k []).map f) →
      Bs.flatten.filter q = Cs.flatten.map f
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | B :: Bs, C :: Cs, hl, h => by
    rw [List.flatten_cons, List.flatten_cons, List.filter_append, List.map_append]
    rw [filter_flatten_of q f Bs Cs (by simpa using hl) fun k hk => h (k + 1) (by simp [hk])]
    exact congrArg (· ++ _) (h 0 (by simp))

theorem map_eq_of_getD {α β γ : Type*} (f : α → γ) (g : β → γ) (a : α) (b : β) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (∀ k, k < l₁.length → f (l₁.getD k a) = g (l₂.getD k b)) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | x :: l₁, y :: l₂, hl, h => by
    rw [List.map_cons, List.map_cons,
      map_eq_of_getD f g a b l₁ l₂ (by simpa using hl) fun k hk => h (k + 1) (by simp [hk])]
    exact congrArg (· :: _) (h 0 (by simp))

theorem pickRun_of_blocks (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) (reps xs : List M) (W : List (ℕ × D)) (Bs : List (List M))
    (Ws : List (List (ℕ × D))) (n : ℕ) (hx : xs = Bs.flatten) (hW : W = Ws.flatten)
    (hB : Bs.length = n) (hWn : Ws.length = n)
    (h : ∀ k, k < n →
      pickRunS L₀ inv conj gen reps (Bs.getD k []) (Ws.getD k []) = some (reps, [])) :
    pickRun L₀ inv conj gen reps xs W = some reps := by
  rw [pickRun_eq_S, hx, hW,
    pickRunS_flatten L₀ inv conj gen reps Bs Ws (hB.trans hWn.symm) fun k hk => h k (hB ▸ hk)]
  rfl

theorem filter_of_blocks {α β : Type*} (q : α → Bool) (f : β → α) (xs : List α) (ys : List β)
    (Bs : List (List α)) (ns : List ℕ) (n : ℕ) (hx : xs = Bs.flatten)
    (hB : Bs.length = n) (hC : (cutL ns ys).length = n)
    (h : ∀ k, k < n → (Bs.getD k []).filter q = ((cutL ns ys).getD k []).map f) :
    xs.filter q = ys.map f := by
  rw [hx, ← flatten_cutL ns ys]
  exact filter_flatten_of q f Bs _ (hB.trans hC.symm) fun k hk => h k (hB ▸ hk)

theorem map_of_getD {α β γ : Type*} (f : α → γ) (g : β → γ) (a : α) (b : β) (l₁ : List α)
    (l₂ : List β) (n : ℕ) (h₁ : l₁.length = n) (h₂ : l₂.length = n)
    (h : ∀ k, k < n → f (l₁.getD k a) = g (l₂.getD k b)) : l₁.map f = l₂.map g :=
  map_eq_of_getD f g a b l₁ l₂ (h₁.trans h₂.symm) fun k hk => h k (h₁ ▸ hk)

theorem all_zip_of_getD {α β : Type*} (F : α × β → Bool) (a : α) (b : β) :
    ∀ (l₁ : List α) (l₂ : List β) (n : ℕ), l₁.length = n → l₂.length = n →
      (∀ k, k < n → F (l₁.getD k a, l₂.getD k b) = true) → (l₁.zip l₂).all F = true
  | [], _, _, _, _, _ => by simp
  | _ :: _, [], _, _, _, _ => by simp
  | x :: l₁, y :: l₂, n, h₁, h₂, h => by
    have h0 : F (x, y) = true := h 0 (by simp at h₁; omega)
    rw [List.zip_cons_cons, List.all_cons, h0, Bool.true_and]
    exact all_zip_of_getD F a b l₁ l₂ (n - 1) (by simp at h₁; omega) (by simp at h₂; omega)
      fun k hk => h (k + 1) (by simp at h₁; omega)

end Blocks

theorem productsC_split : ∀ (Ts : List (List (CV 45))), Ts ≠ [] →
    productsC Ts = ((Ts.headD []).map fun t => (productsC Ts.tail).map (t * ·)).flatten
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

@[expose] noncomputable def blkP : List (List (CV 45)) :=
  (tsCP.headD []).map fun t => (productsC tsCP.tail).map (t * ·)

theorem productsP_eq : productsC tsCP = blkP.flatten :=
  productsC_split tsCP (by decide +kernel)

theorem blkP_len : blkP.length = 45 := by decide +kernel

@[expose] def nWP : List ℕ :=
  [43, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 12, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 12, 4, 4, 4, 4,
    12, 4, 4, 4, 4, 4, 4, 12, 12, 12, 12, 12, 12, 12, 12]

@[expose] noncomputable def W0b : List (List (ℕ × List ℕ)) := cutL nWP W0

theorem W0b_len : W0b.length = 45 := by decide +kernel

@[expose] def nCP0 : List ℕ :=
  [48, 0, 48, 0, 0, 0, 0, 0, 48, 0, 48, 0, 0, 48, 0, 0, 48, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0,
    48, 0, 0, 48, 0, 48, 0, 0, 0, 0, 0, 0, 48, 48, 0, 0, 0]

theorem cutP_0_len : (cutL nCP0 (C0.getD 0 [])).length =
    45 := by decide +kernel

@[expose] def nCP1 : List ℕ :=
  [48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48]

theorem cutP_1_len : (cutL nCP1 (C0.getD 1 [])).length =
    45 := by decide +kernel

theorem chkP_0 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 0 []) (W0b.getD 0 []) = some (reps0, []) ∧
    (blkP.getD 0 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 0 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 0 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 0 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_1 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 1 []) (W0b.getD 1 []) = some (reps0, []) ∧
    (blkP.getD 1 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 1 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 1 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 1 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_2 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 2 []) (W0b.getD 2 []) = some (reps0, []) ∧
    (blkP.getD 2 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 2 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 2 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 2 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_3 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 3 []) (W0b.getD 3 []) = some (reps0, []) ∧
    (blkP.getD 3 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 3 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 3 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 3 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_4 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 4 []) (W0b.getD 4 []) = some (reps0, []) ∧
    (blkP.getD 4 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 4 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 4 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 4 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_5 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 5 []) (W0b.getD 5 []) = some (reps0, []) ∧
    (blkP.getD 5 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 5 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 5 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 5 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_6 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 6 []) (W0b.getD 6 []) = some (reps0, []) ∧
    (blkP.getD 6 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 6 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 6 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 6 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_7 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 7 []) (W0b.getD 7 []) = some (reps0, []) ∧
    (blkP.getD 7 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 7 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 7 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 7 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_8 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 8 []) (W0b.getD 8 []) = some (reps0, []) ∧
    (blkP.getD 8 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 8 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 8 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 8 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_9 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 9 []) (W0b.getD 9 []) = some (reps0, []) ∧
    (blkP.getD 9 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 9 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 9 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 9 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_10 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 10 []) (W0b.getD 10 []) = some (reps0, []) ∧
    (blkP.getD 10 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 10 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 10 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 10 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_11 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 11 []) (W0b.getD 11 []) = some (reps0, []) ∧
    (blkP.getD 11 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 11 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 11 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 11 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_12 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 12 []) (W0b.getD 12 []) = some (reps0, []) ∧
    (blkP.getD 12 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 12 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 12 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 12 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_13 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 13 []) (W0b.getD 13 []) = some (reps0, []) ∧
    (blkP.getD 13 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 13 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 13 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 13 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_14 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 14 []) (W0b.getD 14 []) = some (reps0, []) ∧
    (blkP.getD 14 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 14 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 14 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 14 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_15 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 15 []) (W0b.getD 15 []) = some (reps0, []) ∧
    (blkP.getD 15 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 15 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 15 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 15 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_16 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 16 []) (W0b.getD 16 []) = some (reps0, []) ∧
    (blkP.getD 16 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 16 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 16 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 16 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_17 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 17 []) (W0b.getD 17 []) = some (reps0, []) ∧
    (blkP.getD 17 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 17 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 17 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 17 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_18 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 18 []) (W0b.getD 18 []) = some (reps0, []) ∧
    (blkP.getD 18 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 18 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 18 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 18 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_19 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 19 []) (W0b.getD 19 []) = some (reps0, []) ∧
    (blkP.getD 19 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 19 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 19 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 19 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_20 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 20 []) (W0b.getD 20 []) = some (reps0, []) ∧
    (blkP.getD 20 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 20 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 20 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 20 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_21 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 21 []) (W0b.getD 21 []) = some (reps0, []) ∧
    (blkP.getD 21 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 21 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 21 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 21 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_22 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 22 []) (W0b.getD 22 []) = some (reps0, []) ∧
    (blkP.getD 22 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 22 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 22 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 22 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_23 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 23 []) (W0b.getD 23 []) = some (reps0, []) ∧
    (blkP.getD 23 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 23 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 23 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 23 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_24 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 24 []) (W0b.getD 24 []) = some (reps0, []) ∧
    (blkP.getD 24 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 24 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 24 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 24 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_25 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 25 []) (W0b.getD 25 []) = some (reps0, []) ∧
    (blkP.getD 25 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 25 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 25 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 25 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_26 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 26 []) (W0b.getD 26 []) = some (reps0, []) ∧
    (blkP.getD 26 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 26 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 26 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 26 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_27 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 27 []) (W0b.getD 27 []) = some (reps0, []) ∧
    (blkP.getD 27 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 27 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 27 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 27 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_28 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 28 []) (W0b.getD 28 []) = some (reps0, []) ∧
    (blkP.getD 28 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 28 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 28 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 28 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_29 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 29 []) (W0b.getD 29 []) = some (reps0, []) ∧
    (blkP.getD 29 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 29 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 29 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 29 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_30 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 30 []) (W0b.getD 30 []) = some (reps0, []) ∧
    (blkP.getD 30 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 30 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 30 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 30 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_31 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 31 []) (W0b.getD 31 []) = some (reps0, []) ∧
    (blkP.getD 31 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 31 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 31 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 31 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_32 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 32 []) (W0b.getD 32 []) = some (reps0, []) ∧
    (blkP.getD 32 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 32 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 32 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 32 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_33 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 33 []) (W0b.getD 33 []) = some (reps0, []) ∧
    (blkP.getD 33 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 33 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 33 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 33 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_34 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 34 []) (W0b.getD 34 []) = some (reps0, []) ∧
    (blkP.getD 34 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 34 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 34 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 34 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_35 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 35 []) (W0b.getD 35 []) = some (reps0, []) ∧
    (blkP.getD 35 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 35 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 35 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 35 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_36 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 36 []) (W0b.getD 36 []) = some (reps0, []) ∧
    (blkP.getD 36 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 36 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 36 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 36 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_37 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 37 []) (W0b.getD 37 []) = some (reps0, []) ∧
    (blkP.getD 37 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 37 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 37 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 37 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_38 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 38 []) (W0b.getD 38 []) = some (reps0, []) ∧
    (blkP.getD 38 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 38 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 38 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 38 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_39 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 39 []) (W0b.getD 39 []) = some (reps0, []) ∧
    (blkP.getD 39 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 39 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 39 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 39 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_40 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 40 []) (W0b.getD 40 []) = some (reps0, []) ∧
    (blkP.getD 40 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 40 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 40 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 40 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_41 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 41 []) (W0b.getD 41 []) = some (reps0, []) ∧
    (blkP.getD 41 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 41 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 41 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 41 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_42 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 42 []) (W0b.getD 42 []) = some (reps0, []) ∧
    (blkP.getD 42 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 42 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 42 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 42 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_43 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 43 []) (W0b.getD 43 []) = some (reps0, []) ∧
    (blkP.getD 43 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 43 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 43 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 43 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem chkP_44 :
    pickRunS (productsC tsCP) invC conjC (genP tsCP) reps0
      (blkP.getD 44 []) (W0b.getD 44 []) = some (reps0, []) ∧
    (blkP.getD 44 []).filter
      (fun c => eq22C c (reps0.getD 0 1) (reps0.getD 0 1) c) =
      ((cutL nCP0 (C0.getD 0 [])).getD 44 []).map
        (fun d => (genP tsCP d).getD 1) ∧
    (blkP.getD 44 []).filter
      (fun c => eq22C c (reps0.getD 1 1) (reps0.getD 1 1) c) =
      ((cutL nCP1 (C0.getD 1 [])).getD 44 []).map
        (fun d => (genP tsCP d).getD 1) := by decide +kernel

theorem cov0 : pickRun (elemsC PSp43.QP45) invC conjC (genC PSp43.QP45) reps0
    (elemsC PSp43.QP45) W0 = some reps0 := by
  rw [elemsQP_eq, genP0_eq]
  exact pickRun_of_blocks _ _ _ _ _ _ _ blkP W0b 45 productsP_eq
    (flatten_cutL _ _).symm blkP_len W0b_len fun k hk => match k, hk with
    | 0, _ => (chkP_0).1
    | 1, _ => (chkP_1).1
    | 2, _ => (chkP_2).1
    | 3, _ => (chkP_3).1
    | 4, _ => (chkP_4).1
    | 5, _ => (chkP_5).1
    | 6, _ => (chkP_6).1
    | 7, _ => (chkP_7).1
    | 8, _ => (chkP_8).1
    | 9, _ => (chkP_9).1
    | 10, _ => (chkP_10).1
    | 11, _ => (chkP_11).1
    | 12, _ => (chkP_12).1
    | 13, _ => (chkP_13).1
    | 14, _ => (chkP_14).1
    | 15, _ => (chkP_15).1
    | 16, _ => (chkP_16).1
    | 17, _ => (chkP_17).1
    | 18, _ => (chkP_18).1
    | 19, _ => (chkP_19).1
    | 20, _ => (chkP_20).1
    | 21, _ => (chkP_21).1
    | 22, _ => (chkP_22).1
    | 23, _ => (chkP_23).1
    | 24, _ => (chkP_24).1
    | 25, _ => (chkP_25).1
    | 26, _ => (chkP_26).1
    | 27, _ => (chkP_27).1
    | 28, _ => (chkP_28).1
    | 29, _ => (chkP_29).1
    | 30, _ => (chkP_30).1
    | 31, _ => (chkP_31).1
    | 32, _ => (chkP_32).1
    | 33, _ => (chkP_33).1
    | 34, _ => (chkP_34).1
    | 35, _ => (chkP_35).1
    | 36, _ => (chkP_36).1
    | 37, _ => (chkP_37).1
    | 38, _ => (chkP_38).1
    | 39, _ => (chkP_39).1
    | 40, _ => (chkP_40).1
    | 41, _ => (chkP_41).1
    | 42, _ => (chkP_42).1
    | 43, _ => (chkP_43).1
    | 44, _ => (chkP_44).1
    | k + 45, hk => absurd hk (by omega)

theorem cenP_0 : centC (productsC tsCP) (reps0.getD 0 1) =
    (C0.getD 0 []).map (fun d => (genP tsCP d).getD 1) :=
  filter_of_blocks _ _ _ _ blkP nCP0 45 productsP_eq blkP_len cutP_0_len
    fun k hk => match k, hk with
    | 0, _ => (chkP_0).2.1
    | 1, _ => (chkP_1).2.1
    | 2, _ => (chkP_2).2.1
    | 3, _ => (chkP_3).2.1
    | 4, _ => (chkP_4).2.1
    | 5, _ => (chkP_5).2.1
    | 6, _ => (chkP_6).2.1
    | 7, _ => (chkP_7).2.1
    | 8, _ => (chkP_8).2.1
    | 9, _ => (chkP_9).2.1
    | 10, _ => (chkP_10).2.1
    | 11, _ => (chkP_11).2.1
    | 12, _ => (chkP_12).2.1
    | 13, _ => (chkP_13).2.1
    | 14, _ => (chkP_14).2.1
    | 15, _ => (chkP_15).2.1
    | 16, _ => (chkP_16).2.1
    | 17, _ => (chkP_17).2.1
    | 18, _ => (chkP_18).2.1
    | 19, _ => (chkP_19).2.1
    | 20, _ => (chkP_20).2.1
    | 21, _ => (chkP_21).2.1
    | 22, _ => (chkP_22).2.1
    | 23, _ => (chkP_23).2.1
    | 24, _ => (chkP_24).2.1
    | 25, _ => (chkP_25).2.1
    | 26, _ => (chkP_26).2.1
    | 27, _ => (chkP_27).2.1
    | 28, _ => (chkP_28).2.1
    | 29, _ => (chkP_29).2.1
    | 30, _ => (chkP_30).2.1
    | 31, _ => (chkP_31).2.1
    | 32, _ => (chkP_32).2.1
    | 33, _ => (chkP_33).2.1
    | 34, _ => (chkP_34).2.1
    | 35, _ => (chkP_35).2.1
    | 36, _ => (chkP_36).2.1
    | 37, _ => (chkP_37).2.1
    | 38, _ => (chkP_38).2.1
    | 39, _ => (chkP_39).2.1
    | 40, _ => (chkP_40).2.1
    | 41, _ => (chkP_41).2.1
    | 42, _ => (chkP_42).2.1
    | 43, _ => (chkP_43).2.1
    | 44, _ => (chkP_44).2.1
    | k + 45, hk => absurd hk (by omega)

theorem cenP_1 : centC (productsC tsCP) (reps0.getD 1 1) =
    (C0.getD 1 []).map (fun d => (genP tsCP d).getD 1) :=
  filter_of_blocks _ _ _ _ blkP nCP1 45 productsP_eq blkP_len cutP_1_len
    fun k hk => match k, hk with
    | 0, _ => (chkP_0).2.2
    | 1, _ => (chkP_1).2.2
    | 2, _ => (chkP_2).2.2
    | 3, _ => (chkP_3).2.2
    | 4, _ => (chkP_4).2.2
    | 5, _ => (chkP_5).2.2
    | 6, _ => (chkP_6).2.2
    | 7, _ => (chkP_7).2.2
    | 8, _ => (chkP_8).2.2
    | 9, _ => (chkP_9).2.2
    | 10, _ => (chkP_10).2.2
    | 11, _ => (chkP_11).2.2
    | 12, _ => (chkP_12).2.2
    | 13, _ => (chkP_13).2.2
    | 14, _ => (chkP_14).2.2
    | 15, _ => (chkP_15).2.2
    | 16, _ => (chkP_16).2.2
    | 17, _ => (chkP_17).2.2
    | 18, _ => (chkP_18).2.2
    | 19, _ => (chkP_19).2.2
    | 20, _ => (chkP_20).2.2
    | 21, _ => (chkP_21).2.2
    | 22, _ => (chkP_22).2.2
    | 23, _ => (chkP_23).2.2
    | 24, _ => (chkP_24).2.2
    | 25, _ => (chkP_25).2.2
    | 26, _ => (chkP_26).2.2
    | 27, _ => (chkP_27).2.2
    | 28, _ => (chkP_28).2.2
    | 29, _ => (chkP_29).2.2
    | 30, _ => (chkP_30).2.2
    | 31, _ => (chkP_31).2.2
    | 32, _ => (chkP_32).2.2
    | 33, _ => (chkP_33).2.2
    | 34, _ => (chkP_34).2.2
    | 35, _ => (chkP_35).2.2
    | 36, _ => (chkP_36).2.2
    | 37, _ => (chkP_37).2.2
    | 38, _ => (chkP_38).2.2
    | 39, _ => (chkP_39).2.2
    | 40, _ => (chkP_40).2.2
    | 41, _ => (chkP_41).2.2
    | 42, _ => (chkP_42).2.2
    | 43, _ => (chkP_43).2.2
    | 44, _ => (chkP_44).2.2
    | k + 45, hk => absurd hk (by omega)

theorem cent0_ok : reps0.map (centC (elemsC PSp43.QP45)) = cents0 := by
  rw [elemsQP_eq, cents0_eq]
  exact map_of_getD _ _ 1 [] reps0 C0 2 rfl (by decide +kernel)
    fun r hr => match r, hr with
    | 0, _ => cenP_0
    | 1, _ => cenP_1
    | r + 2, hr => absurd hr (by omega)

@[expose] noncomputable def blkA : List (List (CV 45)) :=
  (tsCA.headD []).map fun t => (productsC tsCA.tail).map (t * ·)

theorem productsA_eq : productsC tsCA = blkA.flatten :=
  productsC_split tsCA (by decide +kernel)

theorem blkA_len : blkA.length = 45 := by decide +kernel

@[expose] def nWA : List ℕ :=
  [139, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 20, 16, 16, 16, 16,
    16, 16, 16, 16, 20, 16, 16, 20, 16, 16, 16, 16, 20, 16, 16, 20, 20, 20, 20, 20, 20, 20]

@[expose] noncomputable def WAb : List (List (ℕ × List ℕ)) := cutL nWA WA

theorem WAb_len : WAb.length = 45 := by decide +kernel

@[expose] def nCA0 : List ℕ :=
  [96, 0, 96, 0, 0, 0, 0, 0, 0, 96, 0, 0, 96, 96, 0, 0, 0, 96, 0, 0, 96, 0, 96, 0, 0, 0, 0,
    0, 96, 0, 0, 0, 0, 0, 96, 0, 96, 0, 0, 0, 96, 0, 0, 0]

theorem cutA_0_len : (cutL nCA0 (CA.getD 0 [])).length =
    45 := by decide +kernel

@[expose] def nCA1 : List ℕ :=
  [96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0]

theorem cutA_1_len : (cutL nCA1 (CA.getD 1 [])).length =
    45 := by decide +kernel

@[expose] def nCA2 : List ℕ :=
  [96, 96, 96, 96, 0, 96, 0, 0, 96, 96, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 96, 96, 96, 96]

theorem cutA_2_len : (cutL nCA2 (CA.getD 2 [])).length =
    45 := by decide +kernel

@[expose] def nCA3 : List ℕ :=
  [16, 0, 16, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0]

theorem cutA_3_len : (cutL nCA3 (CA.getD 3 [])).length =
    45 := by decide +kernel

theorem chkA_0 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 0 []) (WAb.getD 0 []) = some (repsA, []) ∧
    (blkA.getD 0 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 0 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 0 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 0 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 0 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 0 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 0 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 0 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_1 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 1 []) (WAb.getD 1 []) = some (repsA, []) ∧
    (blkA.getD 1 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 1 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 1 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 1 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 1 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 1 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 1 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 1 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_2 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 2 []) (WAb.getD 2 []) = some (repsA, []) ∧
    (blkA.getD 2 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 2 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 2 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 2 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 2 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 2 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 2 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 2 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_3 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 3 []) (WAb.getD 3 []) = some (repsA, []) ∧
    (blkA.getD 3 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 3 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 3 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 3 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 3 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 3 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 3 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 3 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_4 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 4 []) (WAb.getD 4 []) = some (repsA, []) ∧
    (blkA.getD 4 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 4 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 4 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 4 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 4 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 4 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 4 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 4 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_5 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 5 []) (WAb.getD 5 []) = some (repsA, []) ∧
    (blkA.getD 5 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 5 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 5 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 5 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 5 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 5 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 5 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 5 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_6 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 6 []) (WAb.getD 6 []) = some (repsA, []) ∧
    (blkA.getD 6 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 6 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 6 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 6 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 6 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 6 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 6 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 6 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_7 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 7 []) (WAb.getD 7 []) = some (repsA, []) ∧
    (blkA.getD 7 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 7 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 7 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 7 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 7 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 7 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 7 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 7 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_8 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 8 []) (WAb.getD 8 []) = some (repsA, []) ∧
    (blkA.getD 8 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 8 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 8 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 8 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 8 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 8 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 8 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 8 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_9 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 9 []) (WAb.getD 9 []) = some (repsA, []) ∧
    (blkA.getD 9 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 9 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 9 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 9 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 9 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 9 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 9 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 9 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_10 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 10 []) (WAb.getD 10 []) = some (repsA, []) ∧
    (blkA.getD 10 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 10 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 10 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 10 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 10 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 10 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 10 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 10 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_11 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 11 []) (WAb.getD 11 []) = some (repsA, []) ∧
    (blkA.getD 11 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 11 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 11 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 11 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 11 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 11 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 11 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 11 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_12 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 12 []) (WAb.getD 12 []) = some (repsA, []) ∧
    (blkA.getD 12 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 12 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 12 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 12 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 12 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 12 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 12 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 12 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_13 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 13 []) (WAb.getD 13 []) = some (repsA, []) ∧
    (blkA.getD 13 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 13 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 13 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 13 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 13 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 13 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 13 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 13 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_14 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 14 []) (WAb.getD 14 []) = some (repsA, []) ∧
    (blkA.getD 14 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 14 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 14 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 14 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 14 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 14 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 14 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 14 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_15 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 15 []) (WAb.getD 15 []) = some (repsA, []) ∧
    (blkA.getD 15 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 15 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 15 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 15 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 15 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 15 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 15 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 15 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_16 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 16 []) (WAb.getD 16 []) = some (repsA, []) ∧
    (blkA.getD 16 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 16 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 16 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 16 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 16 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 16 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 16 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 16 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_17 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 17 []) (WAb.getD 17 []) = some (repsA, []) ∧
    (blkA.getD 17 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 17 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 17 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 17 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 17 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 17 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 17 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 17 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_18 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 18 []) (WAb.getD 18 []) = some (repsA, []) ∧
    (blkA.getD 18 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 18 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 18 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 18 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 18 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 18 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 18 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 18 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_19 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 19 []) (WAb.getD 19 []) = some (repsA, []) ∧
    (blkA.getD 19 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 19 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 19 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 19 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 19 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 19 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 19 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 19 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_20 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 20 []) (WAb.getD 20 []) = some (repsA, []) ∧
    (blkA.getD 20 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 20 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 20 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 20 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 20 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 20 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 20 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 20 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_21 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 21 []) (WAb.getD 21 []) = some (repsA, []) ∧
    (blkA.getD 21 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 21 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 21 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 21 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 21 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 21 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 21 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 21 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_22 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 22 []) (WAb.getD 22 []) = some (repsA, []) ∧
    (blkA.getD 22 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 22 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 22 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 22 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 22 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 22 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 22 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 22 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_23 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 23 []) (WAb.getD 23 []) = some (repsA, []) ∧
    (blkA.getD 23 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 23 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 23 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 23 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 23 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 23 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 23 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 23 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_24 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 24 []) (WAb.getD 24 []) = some (repsA, []) ∧
    (blkA.getD 24 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 24 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 24 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 24 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 24 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 24 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 24 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 24 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_25 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 25 []) (WAb.getD 25 []) = some (repsA, []) ∧
    (blkA.getD 25 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 25 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 25 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 25 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 25 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 25 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 25 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 25 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_26 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 26 []) (WAb.getD 26 []) = some (repsA, []) ∧
    (blkA.getD 26 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 26 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 26 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 26 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 26 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 26 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 26 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 26 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_27 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 27 []) (WAb.getD 27 []) = some (repsA, []) ∧
    (blkA.getD 27 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 27 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 27 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 27 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 27 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 27 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 27 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 27 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_28 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 28 []) (WAb.getD 28 []) = some (repsA, []) ∧
    (blkA.getD 28 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 28 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 28 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 28 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 28 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 28 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 28 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 28 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_29 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 29 []) (WAb.getD 29 []) = some (repsA, []) ∧
    (blkA.getD 29 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 29 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 29 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 29 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 29 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 29 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 29 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 29 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_30 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 30 []) (WAb.getD 30 []) = some (repsA, []) ∧
    (blkA.getD 30 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 30 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 30 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 30 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 30 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 30 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 30 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 30 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_31 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 31 []) (WAb.getD 31 []) = some (repsA, []) ∧
    (blkA.getD 31 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 31 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 31 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 31 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 31 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 31 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 31 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 31 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_32 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 32 []) (WAb.getD 32 []) = some (repsA, []) ∧
    (blkA.getD 32 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 32 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 32 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 32 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 32 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 32 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 32 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 32 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_33 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 33 []) (WAb.getD 33 []) = some (repsA, []) ∧
    (blkA.getD 33 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 33 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 33 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 33 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 33 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 33 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 33 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 33 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_34 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 34 []) (WAb.getD 34 []) = some (repsA, []) ∧
    (blkA.getD 34 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 34 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 34 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 34 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 34 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 34 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 34 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 34 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_35 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 35 []) (WAb.getD 35 []) = some (repsA, []) ∧
    (blkA.getD 35 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 35 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 35 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 35 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 35 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 35 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 35 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 35 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_36 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 36 []) (WAb.getD 36 []) = some (repsA, []) ∧
    (blkA.getD 36 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 36 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 36 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 36 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 36 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 36 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 36 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 36 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_37 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 37 []) (WAb.getD 37 []) = some (repsA, []) ∧
    (blkA.getD 37 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 37 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 37 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 37 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 37 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 37 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 37 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 37 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_38 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 38 []) (WAb.getD 38 []) = some (repsA, []) ∧
    (blkA.getD 38 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 38 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 38 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 38 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 38 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 38 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 38 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 38 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_39 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 39 []) (WAb.getD 39 []) = some (repsA, []) ∧
    (blkA.getD 39 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 39 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 39 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 39 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 39 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 39 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 39 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 39 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_40 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 40 []) (WAb.getD 40 []) = some (repsA, []) ∧
    (blkA.getD 40 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 40 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 40 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 40 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 40 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 40 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 40 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 40 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_41 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 41 []) (WAb.getD 41 []) = some (repsA, []) ∧
    (blkA.getD 41 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 41 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 41 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 41 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 41 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 41 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 41 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 41 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_42 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 42 []) (WAb.getD 42 []) = some (repsA, []) ∧
    (blkA.getD 42 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 42 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 42 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 42 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 42 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 42 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 42 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 42 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_43 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 43 []) (WAb.getD 43 []) = some (repsA, []) ∧
    (blkA.getD 43 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 43 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 43 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 43 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 43 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 43 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 43 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 43 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem chkA_44 :
    pickRunS (productsC tsCA) invC conjC (genP tsCA) repsA
      (blkA.getD 44 []) (WAb.getD 44 []) = some (repsA, []) ∧
    (blkA.getD 44 []).filter
      (fun c => eq22C c (repsA.getD 0 1) (repsA.getD 0 1) c) =
      ((cutL nCA0 (CA.getD 0 [])).getD 44 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 44 []).filter
      (fun c => eq22C c (repsA.getD 1 1) (repsA.getD 1 1) c) =
      ((cutL nCA1 (CA.getD 1 [])).getD 44 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 44 []).filter
      (fun c => eq22C c (repsA.getD 2 1) (repsA.getD 2 1) c) =
      ((cutL nCA2 (CA.getD 2 [])).getD 44 []).map
        (fun d => (genP tsCA d).getD 1) ∧
    (blkA.getD 44 []).filter
      (fun c => eq22C c (repsA.getD 3 1) (repsA.getD 3 1) c) =
      ((cutL nCA3 (CA.getD 3 [])).getD 44 []).map
        (fun d => (genP tsCA d).getD 1) := by decide +kernel

theorem covA : pickRun (elemsC PSp43.QA45) invC conjC (genC PSp43.QA45) repsA
    (elemsC PSp43.QA45) WA = some repsA := by
  rw [elemsQA_eq, genPA_eq]
  exact pickRun_of_blocks _ _ _ _ _ _ _ blkA WAb 45 productsA_eq
    (flatten_cutL _ _).symm blkA_len WAb_len fun k hk => match k, hk with
    | 0, _ => (chkA_0).1
    | 1, _ => (chkA_1).1
    | 2, _ => (chkA_2).1
    | 3, _ => (chkA_3).1
    | 4, _ => (chkA_4).1
    | 5, _ => (chkA_5).1
    | 6, _ => (chkA_6).1
    | 7, _ => (chkA_7).1
    | 8, _ => (chkA_8).1
    | 9, _ => (chkA_9).1
    | 10, _ => (chkA_10).1
    | 11, _ => (chkA_11).1
    | 12, _ => (chkA_12).1
    | 13, _ => (chkA_13).1
    | 14, _ => (chkA_14).1
    | 15, _ => (chkA_15).1
    | 16, _ => (chkA_16).1
    | 17, _ => (chkA_17).1
    | 18, _ => (chkA_18).1
    | 19, _ => (chkA_19).1
    | 20, _ => (chkA_20).1
    | 21, _ => (chkA_21).1
    | 22, _ => (chkA_22).1
    | 23, _ => (chkA_23).1
    | 24, _ => (chkA_24).1
    | 25, _ => (chkA_25).1
    | 26, _ => (chkA_26).1
    | 27, _ => (chkA_27).1
    | 28, _ => (chkA_28).1
    | 29, _ => (chkA_29).1
    | 30, _ => (chkA_30).1
    | 31, _ => (chkA_31).1
    | 32, _ => (chkA_32).1
    | 33, _ => (chkA_33).1
    | 34, _ => (chkA_34).1
    | 35, _ => (chkA_35).1
    | 36, _ => (chkA_36).1
    | 37, _ => (chkA_37).1
    | 38, _ => (chkA_38).1
    | 39, _ => (chkA_39).1
    | 40, _ => (chkA_40).1
    | 41, _ => (chkA_41).1
    | 42, _ => (chkA_42).1
    | 43, _ => (chkA_43).1
    | 44, _ => (chkA_44).1
    | k + 45, hk => absurd hk (by omega)

theorem cenA_0 : centC (productsC tsCA) (repsA.getD 0 1) =
    (CA.getD 0 []).map (fun d => (genP tsCA d).getD 1) :=
  filter_of_blocks _ _ _ _ blkA nCA0 45 productsA_eq blkA_len cutA_0_len
    fun k hk => match k, hk with
    | 0, _ => (chkA_0).2.1
    | 1, _ => (chkA_1).2.1
    | 2, _ => (chkA_2).2.1
    | 3, _ => (chkA_3).2.1
    | 4, _ => (chkA_4).2.1
    | 5, _ => (chkA_5).2.1
    | 6, _ => (chkA_6).2.1
    | 7, _ => (chkA_7).2.1
    | 8, _ => (chkA_8).2.1
    | 9, _ => (chkA_9).2.1
    | 10, _ => (chkA_10).2.1
    | 11, _ => (chkA_11).2.1
    | 12, _ => (chkA_12).2.1
    | 13, _ => (chkA_13).2.1
    | 14, _ => (chkA_14).2.1
    | 15, _ => (chkA_15).2.1
    | 16, _ => (chkA_16).2.1
    | 17, _ => (chkA_17).2.1
    | 18, _ => (chkA_18).2.1
    | 19, _ => (chkA_19).2.1
    | 20, _ => (chkA_20).2.1
    | 21, _ => (chkA_21).2.1
    | 22, _ => (chkA_22).2.1
    | 23, _ => (chkA_23).2.1
    | 24, _ => (chkA_24).2.1
    | 25, _ => (chkA_25).2.1
    | 26, _ => (chkA_26).2.1
    | 27, _ => (chkA_27).2.1
    | 28, _ => (chkA_28).2.1
    | 29, _ => (chkA_29).2.1
    | 30, _ => (chkA_30).2.1
    | 31, _ => (chkA_31).2.1
    | 32, _ => (chkA_32).2.1
    | 33, _ => (chkA_33).2.1
    | 34, _ => (chkA_34).2.1
    | 35, _ => (chkA_35).2.1
    | 36, _ => (chkA_36).2.1
    | 37, _ => (chkA_37).2.1
    | 38, _ => (chkA_38).2.1
    | 39, _ => (chkA_39).2.1
    | 40, _ => (chkA_40).2.1
    | 41, _ => (chkA_41).2.1
    | 42, _ => (chkA_42).2.1
    | 43, _ => (chkA_43).2.1
    | 44, _ => (chkA_44).2.1
    | k + 45, hk => absurd hk (by omega)

theorem cenA_1 : centC (productsC tsCA) (repsA.getD 1 1) =
    (CA.getD 1 []).map (fun d => (genP tsCA d).getD 1) :=
  filter_of_blocks _ _ _ _ blkA nCA1 45 productsA_eq blkA_len cutA_1_len
    fun k hk => match k, hk with
    | 0, _ => (chkA_0).2.2.1
    | 1, _ => (chkA_1).2.2.1
    | 2, _ => (chkA_2).2.2.1
    | 3, _ => (chkA_3).2.2.1
    | 4, _ => (chkA_4).2.2.1
    | 5, _ => (chkA_5).2.2.1
    | 6, _ => (chkA_6).2.2.1
    | 7, _ => (chkA_7).2.2.1
    | 8, _ => (chkA_8).2.2.1
    | 9, _ => (chkA_9).2.2.1
    | 10, _ => (chkA_10).2.2.1
    | 11, _ => (chkA_11).2.2.1
    | 12, _ => (chkA_12).2.2.1
    | 13, _ => (chkA_13).2.2.1
    | 14, _ => (chkA_14).2.2.1
    | 15, _ => (chkA_15).2.2.1
    | 16, _ => (chkA_16).2.2.1
    | 17, _ => (chkA_17).2.2.1
    | 18, _ => (chkA_18).2.2.1
    | 19, _ => (chkA_19).2.2.1
    | 20, _ => (chkA_20).2.2.1
    | 21, _ => (chkA_21).2.2.1
    | 22, _ => (chkA_22).2.2.1
    | 23, _ => (chkA_23).2.2.1
    | 24, _ => (chkA_24).2.2.1
    | 25, _ => (chkA_25).2.2.1
    | 26, _ => (chkA_26).2.2.1
    | 27, _ => (chkA_27).2.2.1
    | 28, _ => (chkA_28).2.2.1
    | 29, _ => (chkA_29).2.2.1
    | 30, _ => (chkA_30).2.2.1
    | 31, _ => (chkA_31).2.2.1
    | 32, _ => (chkA_32).2.2.1
    | 33, _ => (chkA_33).2.2.1
    | 34, _ => (chkA_34).2.2.1
    | 35, _ => (chkA_35).2.2.1
    | 36, _ => (chkA_36).2.2.1
    | 37, _ => (chkA_37).2.2.1
    | 38, _ => (chkA_38).2.2.1
    | 39, _ => (chkA_39).2.2.1
    | 40, _ => (chkA_40).2.2.1
    | 41, _ => (chkA_41).2.2.1
    | 42, _ => (chkA_42).2.2.1
    | 43, _ => (chkA_43).2.2.1
    | 44, _ => (chkA_44).2.2.1
    | k + 45, hk => absurd hk (by omega)

theorem cenA_2 : centC (productsC tsCA) (repsA.getD 2 1) =
    (CA.getD 2 []).map (fun d => (genP tsCA d).getD 1) :=
  filter_of_blocks _ _ _ _ blkA nCA2 45 productsA_eq blkA_len cutA_2_len
    fun k hk => match k, hk with
    | 0, _ => (chkA_0).2.2.2.1
    | 1, _ => (chkA_1).2.2.2.1
    | 2, _ => (chkA_2).2.2.2.1
    | 3, _ => (chkA_3).2.2.2.1
    | 4, _ => (chkA_4).2.2.2.1
    | 5, _ => (chkA_5).2.2.2.1
    | 6, _ => (chkA_6).2.2.2.1
    | 7, _ => (chkA_7).2.2.2.1
    | 8, _ => (chkA_8).2.2.2.1
    | 9, _ => (chkA_9).2.2.2.1
    | 10, _ => (chkA_10).2.2.2.1
    | 11, _ => (chkA_11).2.2.2.1
    | 12, _ => (chkA_12).2.2.2.1
    | 13, _ => (chkA_13).2.2.2.1
    | 14, _ => (chkA_14).2.2.2.1
    | 15, _ => (chkA_15).2.2.2.1
    | 16, _ => (chkA_16).2.2.2.1
    | 17, _ => (chkA_17).2.2.2.1
    | 18, _ => (chkA_18).2.2.2.1
    | 19, _ => (chkA_19).2.2.2.1
    | 20, _ => (chkA_20).2.2.2.1
    | 21, _ => (chkA_21).2.2.2.1
    | 22, _ => (chkA_22).2.2.2.1
    | 23, _ => (chkA_23).2.2.2.1
    | 24, _ => (chkA_24).2.2.2.1
    | 25, _ => (chkA_25).2.2.2.1
    | 26, _ => (chkA_26).2.2.2.1
    | 27, _ => (chkA_27).2.2.2.1
    | 28, _ => (chkA_28).2.2.2.1
    | 29, _ => (chkA_29).2.2.2.1
    | 30, _ => (chkA_30).2.2.2.1
    | 31, _ => (chkA_31).2.2.2.1
    | 32, _ => (chkA_32).2.2.2.1
    | 33, _ => (chkA_33).2.2.2.1
    | 34, _ => (chkA_34).2.2.2.1
    | 35, _ => (chkA_35).2.2.2.1
    | 36, _ => (chkA_36).2.2.2.1
    | 37, _ => (chkA_37).2.2.2.1
    | 38, _ => (chkA_38).2.2.2.1
    | 39, _ => (chkA_39).2.2.2.1
    | 40, _ => (chkA_40).2.2.2.1
    | 41, _ => (chkA_41).2.2.2.1
    | 42, _ => (chkA_42).2.2.2.1
    | 43, _ => (chkA_43).2.2.2.1
    | 44, _ => (chkA_44).2.2.2.1
    | k + 45, hk => absurd hk (by omega)

theorem cenA_3 : centC (productsC tsCA) (repsA.getD 3 1) =
    (CA.getD 3 []).map (fun d => (genP tsCA d).getD 1) :=
  filter_of_blocks _ _ _ _ blkA nCA3 45 productsA_eq blkA_len cutA_3_len
    fun k hk => match k, hk with
    | 0, _ => (chkA_0).2.2.2.2
    | 1, _ => (chkA_1).2.2.2.2
    | 2, _ => (chkA_2).2.2.2.2
    | 3, _ => (chkA_3).2.2.2.2
    | 4, _ => (chkA_4).2.2.2.2
    | 5, _ => (chkA_5).2.2.2.2
    | 6, _ => (chkA_6).2.2.2.2
    | 7, _ => (chkA_7).2.2.2.2
    | 8, _ => (chkA_8).2.2.2.2
    | 9, _ => (chkA_9).2.2.2.2
    | 10, _ => (chkA_10).2.2.2.2
    | 11, _ => (chkA_11).2.2.2.2
    | 12, _ => (chkA_12).2.2.2.2
    | 13, _ => (chkA_13).2.2.2.2
    | 14, _ => (chkA_14).2.2.2.2
    | 15, _ => (chkA_15).2.2.2.2
    | 16, _ => (chkA_16).2.2.2.2
    | 17, _ => (chkA_17).2.2.2.2
    | 18, _ => (chkA_18).2.2.2.2
    | 19, _ => (chkA_19).2.2.2.2
    | 20, _ => (chkA_20).2.2.2.2
    | 21, _ => (chkA_21).2.2.2.2
    | 22, _ => (chkA_22).2.2.2.2
    | 23, _ => (chkA_23).2.2.2.2
    | 24, _ => (chkA_24).2.2.2.2
    | 25, _ => (chkA_25).2.2.2.2
    | 26, _ => (chkA_26).2.2.2.2
    | 27, _ => (chkA_27).2.2.2.2
    | 28, _ => (chkA_28).2.2.2.2
    | 29, _ => (chkA_29).2.2.2.2
    | 30, _ => (chkA_30).2.2.2.2
    | 31, _ => (chkA_31).2.2.2.2
    | 32, _ => (chkA_32).2.2.2.2
    | 33, _ => (chkA_33).2.2.2.2
    | 34, _ => (chkA_34).2.2.2.2
    | 35, _ => (chkA_35).2.2.2.2
    | 36, _ => (chkA_36).2.2.2.2
    | 37, _ => (chkA_37).2.2.2.2
    | 38, _ => (chkA_38).2.2.2.2
    | 39, _ => (chkA_39).2.2.2.2
    | 40, _ => (chkA_40).2.2.2.2
    | 41, _ => (chkA_41).2.2.2.2
    | 42, _ => (chkA_42).2.2.2.2
    | 43, _ => (chkA_43).2.2.2.2
    | 44, _ => (chkA_44).2.2.2.2
    | k + 45, hk => absurd hk (by omega)

theorem centA_ok : repsA.map (centC (elemsC PSp43.QA45)) = centsA := by
  rw [elemsQA_eq, centsA_eq]
  exact map_of_getD _ _ 1 [] repsA CA 4 rfl (by decide +kernel)
    fun r hr => match r, hr with
    | 0, _ => cenA_0
    | 1, _ => cenA_1
    | 2, _ => cenA_2
    | 3, _ => cenA_3
    | r + 4, hr => absurd hr (by omega)

theorem loc0 : (reps0.zip cents0).all (fun p => noOddB 12 p.2 &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 p.1 p.2) = true := by
  rw [cents0_eq]
  decide +kernel

theorem locA_0 : (noOddB 12 (centsA.getD 0 []) &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 (repsA.getD 0 1) (centsA.getD 0 [])) =
    true := by
  rw [centsA_eq]
  decide +kernel

theorem locA_1 : (noOddB 12 (centsA.getD 1 []) &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 (repsA.getD 1 1) (centsA.getD 1 [])) =
    true := by
  rw [centsA_eq]
  decide +kernel

theorem locA_2 : (noOddB 12 (centsA.getD 2 []) &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 (repsA.getD 2 1) (centsA.getD 2 [])) =
    true := by
  rw [centsA_eq]
  decide +kernel

theorem locA_3 : (noOddB 12 (centsA.getD 3 []) &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 (repsA.getD 3 1) (centsA.getD 3 [])) =
    true := by
  rw [centsA_eq]
  decide +kernel

theorem locA : (repsA.zip centsA).all (fun p => noOddB 12 p.2 &&
    pairChkG (cOf (Certificates.P43Twin.tA ())) Q1 Q2 p.1 p.2) = true :=
  all_zip_of_getD _ 1 [] repsA centsA 4 rfl (by rw [centsA_eq]; decide +kernel)
    fun k hk => match k, hk with
    | 0, _ => locA_0
    | 1, _ => locA_1
    | 2, _ => locA_2
    | 3, _ => locA_3
    | k + 4, hk => absurd hk (by omega)

theorem sigmaChkG_of_centB {M : Type*} [Group M] [DecidableEq M] {Q1 Q2 : List M}
    {a1 a2 x1 x2 t : M} (L : List M) (h1 : t ∈ Q1) (h2 : t ∈ Q2)
    (h : sigmaChkG Q1 Q2 a1 a2 x1 x2 (centB L t) = true) :
    sigmaChkG Q1 Q2 a1 a2 x1 x2 L = true := by
  have hc : ∀ Q : List M, t ∈ Q → centQG (centB L t) Q = centQG L Q := fun Q hQ => by
    unfold centQG centB
    rw [List.filter_filter]
    congr 1
    funext g
    cases hg : Q.all fun q => decide (q * g = g * q)
    · rfl
    · have := of_decide_eq_true (List.all_eq_true.1 hg t hQ)
      simp [this]
  have hm : ∀ x, memB (centB L t) x = true → memB L x = true := fun x hx => by
    unfold memB at hx ⊢
    obtain ⟨s, hs, e⟩ := List.any_eq_true.1 hx
    exact List.any_eq_true.2 ⟨s, (List.mem_filter.1 hs).1, e⟩
  have hall : (Q1 ++ Q2).all (memB (centB L t)) = true → (Q1 ++ Q2).all (memB L) = true :=
    fun ha => List.all_eq_true.2 fun x hx => hm x (List.all_eq_true.1 ha x hx)
  unfold sigmaChkG at h ⊢
  rw [hc Q1 h1, hc Q2 h2] at h
  revert h hall
  generalize (Q1 ++ Q2).all (memB L) = b
  generalize (Q1 ++ Q2).all (memB (centB L t)) = b'
  cases b <;> cases b' <;> simp

theorem head_of_map_eq {α β : Type*} {f : α → β} {a : α} {l : List α} {cs : List β} (d : β)
    (h : (a :: l).map f = cs) : f a = cs.headD d := by
  rw [← h]
  rfl

theorem sigCent : sigmaChkG Q1 Q2 (cOf (Certificates.P43Twin.a1 ()))
    (cOf (Certificates.P43Twin.a2 ())) (cOf (Certificates.P43Twin.x1 ()))
    (cOf (Certificates.P43Twin.x2 ())) (cents0.headD []) = true := by
  rw [cents0_eq]
  decide +kernel

theorem sig : sigmaChkG Q1 Q2 (cOf (Certificates.P43Twin.a1 ())) (cOf (Certificates.P43Twin.a2 ()))
    (cOf (Certificates.P43Twin.x1 ())) (cOf (Certificates.P43Twin.x2 ())) (elemsC PSp43.QP45) =
    true := by
  refine sigmaChkG_of_centB (t := cOf (Certificates.P43Twin.tA ())) _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  have hC : centB (elemsC PSp43.QP45) (cOf (Certificates.P43Twin.tA ())) = cents0.headD [] :=
    (centB_eq_centC _ _).trans (head_of_map_eq [] cent0_ok)
  rw [hC]
  exact sigCent

end Certificates.Kernel.ONanSmall.P43T
