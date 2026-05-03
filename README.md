## JAIDE projekt áttekintése

A JAIDE rendszer egy következő generációs nagy nyelvi modell (LLM) keretrendszer, amelyet úgy terveztek, hogy megkerülje a Transformer architektúra alapvető méretezési korlátait. Az elsősorban Zig-ben épülő JAIDE bevezeti a Reversible Scatter Flow (RSF) architektúrát, amely a memóriaigényes önmegfigyelési mechanizmust bijektív csatolási rétegekkel és fraktálkeveréssel helyettesíti. Ez a kialakítás O(1) memóriakomplexitást tesz lehetővé a visszafelé haladás során, lehetővé téve a rendkívül mély hálózatok (10 000+ réteg) képzését alaphardveren.

### Építészetfilozófia: Paradigma

A JAIDE radikális eltérést jelent az információveszteséget okozó architektúráktól. Míg a hagyományos modellek (CNN, Transformers, Mamba) az információt nem lineáris aktiválással, például ReLU-val vagy poolinggal semmisítik meg, addig a JAIDE 100%-os információmegőrzést biztosít invertálható primitívjei révén

A filozófiai pillérek a következők:

- Matematikai purizmus: A rendszer egyetlen számítási primitívre épül - az affin csatolásra -, amelyet formálisan igazoltak a bijektivitás szempontjából
- Hardveres szimbiózis: A Python overhead megkerülése Zig-native stack használatával, közvetlen Futhark GPU kernel integrációval
- Memóriahatékonyság: A köztes aktiválások tárolásának szükségtelenné tétele, a VRAM-kapacitásról a szűk keresztmetszet áthelyezése a tiszta számítási teljesítményre

### Rendszerarchitektúra és adatáramlás

A következő ábra azt szemlélteti, hogy a természetes nyelvi bemenet hogyan halad át a rendszeren, a magas szintű API-kiszolgálótól az alacsony szintű kódegységekig, amelyek a tenzorokat és a hardveres gyorsítást kezelik.

### Kulcsfontosságú alrendszerek

### 1. Neurális mag: RSF és OFTB

A JAIDE magja az RSF (Reversible Scatter Flow) A LayerCore tenzorokat (s_weight, t_weight, s_bias, t_bias) használja a tökéletesen reverzibilis skálázó- és transzlációs műveletek elvégzésére Az információk dimenziók közötti keverését az OFTB (Orthogonal Fractal Transform Block) kezeli, amely egy rsf_scatter mechanizmust használ a globális kontextus eléréséhez $O(N^2)$ figyelem mátrixok nélkül

### 2. Képzés és optimalizálás

A képzést az SFD (Stochastic Fisher Diagonal) optimalizáló segítségével szervezzük, amely egy másodrendű módszer, amely a gyorsabb konvergencia érdekében közelíti a Fisher Információs Mátrixot. Az elosztott képzést a DistributedTrainerFuthark kezeli, amely az NCCLallReduce segítségével koordinálja a több GPU-s munkaterhelést

### 3. Kognitív relációs motor (CRE)

A szabványos LLM következtetésen túl a JAIDE tartalmaz egy SelfSimilarRelationalGraph (NSIR) alrendszert. Ez az alrendszer az információt kvantumállapotú gráfként kezeli, és az ESSO (Entangled Stochastic Symmetry Optimizer) segítségével optimális relációs leképezéseket talál a fogalmak között.

### 4. Hardver absztrakciós réteg

A JAIDE olyan nagy teljesítményű hardvereket céloz meg, mint az NVIDIA B200 Az accel_interface egységes API-t biztosít a futhark_kernelek számára, míg az RGPU szimuláció lehetővé teszi a relációs gráffeldolgozás tesztelését szimulált aszinkron NoC (Network on Chip) architektúrákon.

- Hogyan használd a build.zig és a modal_setup.sh állományt a környezeted előkészítéséhez.
- Részletes utasítások az HuggingFaceFW/finephrase adatkészlettel való képzésről és az ellenőrző pontok kezeléséről a model_io.zig segítségével
- Neurális magarchitektúra: Zig megvalósításába és a bijektivitás matematikai bizonyításába való elmélyülés.
- Következtetési csővezeték: Részletek az SSI trie-alapú indexelésről és a Ranker újraértékelő motorról
- Core Relational Engine (CRE) (5. szakasz) Az nsir_core.zig és a kvantumlogikai alrendszerek feltárása.
- Hardveres gyorsítás (6. szakasz) Dokumentáció a futhark_kernels.fut és az RGPU relációs processzorhoz.

## Kezdő lépések: Telepítés: Építés, konfigurálás és telepítés

Ez az oldal a JAIDE LLM rendszer forrásból történő felépítéséhez, a hardveres gyorsító rétegek konfigurálásához, valamint a következtetési és képzési munkaterhelések telepítéséhez nyújt technikai dokumentációt. A JAIDE a Zig programozási nyelvet használja a magfuttatási időhöz és a Futhark nyelvet a nagy teljesítményű adatpárhuzamos GPU-kernelekhez.

### Rendszerarchitektúra építése

A JAIDE a Zig Build System (build.zig) segítségével szervezi a Zig forráskód, a C-interop fájlok és a Futhark által generált GPU-kernelek fordítását. A build folyamatot úgy tervezték, hogy optimalizált binárisokat állítson elő különböző végrehajtási módokhoz, beleértve az önálló következtetést, az elosztott képzést és a hardveresen gyorsított GPU-s végrehajtást.

### Építési célok és lehetőségek

A build.zig fájl számos futtatható célprogramot és konfigurációs opciót határoz meg, hogy a bináris programot az adott környezethez igazítsa.

| Cél neve | Gyökérforrás | Leírás |
| --- | --- | --- |
| jaide | src/main.zig | Az elsődleges CLI a helyi végrehajtáshoz és hibakereséshez |
| jaide-inference-server | src/inference_server_main.zig | HTTP szerver a modell előrejelzések kiszolgálásához |
| jaide-distributed | src/main_distributed.zig | Elosztott képzési belépési pont (megköveteli -Dgpu=true) |
| jaide-gpu | src/main_gpu.zig | Optimalizált egy GPU-s képzés/következtetés (megköveteli -Dgpu=true) |

Kulcsfontosságú építési lehetőségek:

- -Doptimize=[Debug|ReleaseSafe|ReleaseFast|ReleaseSmall]: Standard Zig optimalizálási szintek
- -Dgpu=[bool]: GPU/CUDA gyorsítás engedélyezése. Ha igaz, akkor beállítja a gpu_acceleration build opciót a feltételes fordításhoz a Zigben

### Adatáramlás építése

A következő ábra azt szemlélteti, hogy a build rendszer hogyan integrálja a Futhark kerneleket a végleges Zig binárisba.

### GPU gyorsítás konfiguráció

A JAIDE a Futharkra támaszkodik, hogy optimalizált C kódot generáljon, amely a CUDA backendekhez kapcsolódik. Ehhez egy kétlépcsős fordítási folyamatra van szükség, ahol a Futhark forráskódot először C-re fordítjuk, majd belinkeljük a Zig binárisba.

1.   Maggenerálás: A Futhark fordító a futhark_kernels.c és futhark_kernels.h állományokat a .fut forrásból generálja
2.   C-Interop: A Zig build script hozzáadja ezeket a generált fájlokat a fordítási egységhez az addCSourceFile és az addIncludePath segítségével
3.   Optimalizálás: -O2 zászlókkal fordítják a Zig build rendszerben

### Felhő telepítés modálison keresztül

A JAIDE-t kifejezetten az NVIDIA B200 GPU-klaszterekre optimalizálták, mind a képzéshez, mind a következtetések levonásához.

### Infrastruktúra beállítása

A modal_setup.sh szkript inicializálja a szükséges felhőkörnyezetet, beleértve az adatkészletek és a modell ellenőrzőpontok tárolási köteteit.

- Kötetek: Két tartós kötet jön létre: jaide-training-data és jaide-dataset
- Környezetvédelem: A Modal image az nvidia/cuda:12.4.0-devel-ubuntu22.04 rendszeren alapul, és tartalmazza a Zig 0.13.0 és a Futhark-ot

### Elosztott képzési telepítés

A képzést a modal_train.py és a modal_distributed_train.py kezeli, amelyek a több GPU-s munkaterhelést irányítják.

- GPU-konfiguráció: GPU: Alapértelmezés szerint 8x B200 GPU
- Adathalmazok felvétele: A rendszer automatikusan letölti és JSONL formátumba konvertálja a HuggingFaceFW/finephrase adatkészletet a távoli kötetben
- Végrehajtás: A train_jaide függvény kezeli az epochahurkot, a lefordított Zig bináris programot a --mode train jelzővel hívja meg

### Következtetési kiszolgáló

A következtetési kiszolgáló nagy teljesítményű végpontot biztosít a betanított modellekből történő szöveggeneráláshoz. Az src/inference_server_main.zig állományban van implementálva, és az InferenceServer osztályt használja.

### Konfiguráció (ServerConfig)

A kiszolgáló konfigurálása egy ServerConfig struktúrán keresztül történik, amelyet a CLI-argumentumokkal lehet feltölteni

| Paraméter | Alapértelmezett | CLI-jelzés |
| --- | --- | --- |
| port | 8080 | --port |
| host | "0.0.0.0.0" | --host |
| model_path | null | --model |
| batch_size | 32 | N/A |
| require_api_key | false | --require-api-key |

### Következtetés végrehajtása

A szerver inicializálja a modellt, és a server.start() segítségével elkezdi figyelni a kéréseket. A felhőalapú telepítéshez a modal_inference.py csomagolja ezt a funkciót, és egy Python interfészt biztosít a következtetés futtatásához a B200 GPU-kon.

## Képzési útmutató

Ez az útmutató átfogó technikai áttekintést nyújt a JAIDE modellek képzési csővezetékéről. A rendszer egy elosztott, több GPU-s architektúrát használ, amelyet a Modal segítségével szerveznek, kihasználva a Reversible Scatter Flow (RSF) architektúrát a memóriahatékony visszaterjedéshez és a Stochastic Fractal Descent (SFD) optimalizálót a másodrendű optimalizáláshoz.

### Adatbevitel és tokenizálás

A képzési csővezeték a HuggingFaceFW/finephrase adathalmaz bevitelével kezdődik, amelyet az MGT (Morpheme-Guided Tokenization) rendszer számára megfelelő formátumba dolgoznak fel.

### Adatkészlet felvétele

Az adatbeviteli folyamatot a _download_finephrase_to_jsonl kezeli. A program letölti az adathalmazt az Hugging Face datasets könyvtár segítségével, és különböző kulcsokból (szöveg, tartalom, mondat, cikk) kivonatolja a szöveget, hogy létrehozzon egy train.jsonl fájlt, ahol minden sor egy JSON objektum, amely egy "text" mezőt tartalmaz

### MGT Tokenizer

Az MGT (Morpheme-Guided Tokenization) rendszer, amely az src/tokenizer/mgt.zig-ben van definiálva, a nyers szöveg token azonosítókká történő átalakítását kezeli. Előre meghatározott szókinccsel és morfémák (előtagok és utótagok) készletével inicializálódik, hogy kezelje az alszavak bontását

Az MGT fő összetevői:

- Különleges zsetonok: [PAD], [UNK], [BOS] és [EOS]
- Morfémalisták: Az előtagok és utótagok hash-térképek inicializálásához a gyakori előtagok (pl. "un", "re", "pre") és utótagok (pl. "ing", "ed", "tion") előre definiált listáit használják
- Horgonyzási tokenek: A szekvencia indexeléshez és illesztéshez használt kiemelt fontosságú tokenek

### Adatáramlás: Szövegből tokenek

A következő ábra a nyers adatkészlet soraitól a DistributedTrainerFuthark által használt tokenizált tételekig tartó áramlást mutatja be.

### Elosztott képzési infrastruktúra

A JAIDE egy elosztott képzési stratégiát alkalmaz, amely a Modal-t használja a felhőszervezéshez és az NCCL-t a több GPU-s gradiens szinkronizáláshoz.

### Modális hangszerelés

A modal_train.py szkript definiálja a végrehajtási környezetet, beleértve a CUDA 12.4 alapképet, a Zig 0.13.0-t és a Futhark fordítót A modális kötetet éside-training-data-t mountolja a tartós ellenőrzőpontok tárolására

### GPU koordináció

A GPUCoordinator (hivatkozással: kezeli az elosztott állapotot. A rendszer úgy van kialakítva, hogy több NVIDIA B200 GPU-n keresztül skálázható legyen, az NCCL allReduce segítségével szinkronizálja a gradienseket a klaszteren belül

### DistributedTrainerFuthark

A src/distributed/distributed/distributed_trainer_futhark.zig fájlban található DistributedTrainerFuthark struktúra a képzési ciklus elsődleges vezérlője. Integrálja az RSFAccelerátort (GPU-alapú RSF implementáció) az MGT tokenizerrel

Inicializálási paraméterek:

- model_dim: Az RSF rétegek rejtett dimenziója.
- local_batch_size: Batch size per GPU rank.
- learning_rate: Lépésméret az optimalizáláshoz.

### Neurális architektúra és optimalizálás

A képzési folyamat lényege az RSF-architektúra és az SFD-optimalizáló.

### Visszafordítható szórásos áramlás (RSF)

Az RSF-rétegek bijektív csatolást biztosítanak, ami lehetővé teszi a $O(1)$ memóriás visszaterjedést azáltal, hogy az aktivációkat a visszaterjedés során rekonstruálják, ahelyett, hogy tárolnák őket. Ez kritikus fontosságú a nagy modellek nagy memóriájú B200 GPU-kon történő képzéséhez.

### Sztochasztikus fraktál leszállás (SFD)

Az src/optimizer/sfd.zig fájlban implementált SFD optimalizáló fejlett másodrendű optimalizálási funkciókat biztosít:

- Vegyes precizitás: Támogatja az fp4, fp8, fp16 és fp32 kvantálást a B200 Tensor Memory (TMEM) használatának optimalizálása érdekében
- Kvantálási logika: A quantizeValue függvény kezeli az alacsony pontosságú formátumokhoz szükséges szorítást és kerekítést
- Tensormenedzsment: A Tensor struktúra tartalmazza az in_tensor_memory és az is_compressed jelzőket

### Képzési hurok logikája

A képzési ciklus epochákon keresztül ismétlődik, ahol minden epocha a következőket foglalja magában:

1.   Az adatkészlet egy részhalmazának betöltése.
2.   Tokenizálás MGT-n keresztül.
3.   Előrehaladás az RSFAcceleratoron keresztül.
4.   Gradiens számítás és NCCL szinkronizálás.
5.   Súlyfrissítések SFD használatával.
6.   Ellenőrzési pontok a Modal kötetre.

A képzés végrehajtásának folyamata

### Ellenőrzőpont-kezelés

Az ellenőrző pontok egy egyedi formátumot használnak, amelyet a 0x54464453 ("SDFT") bűvös számmal azonosítanak.

### Tárolás és metaadatok

A képzési eredmények és a modellsúlyok a Modal konténerben lévő /models könyvtárban tárolódnak, amely a jaide-training-data kötet által támogatott Minden egyes ellenőrzési pont tartalmazza:

- Modell súlyok: RSF réteg paraméterei.
- Metaadatok: JSON fájl, amely tartalmazza a képzés állapotát, a veszteséget, az időtartamot és a hiperparamétereket

### Modell listázás

A modal_train.py fájl list_models függvénye lehetővé teszi a felhasználók számára, hogy lekérdezzék a mentett ellenőrzőpontokat, olyan részletekkel, mint a fájl mérete és a módosítási időbélyegek

## Neurális magarchitektúra: RSF és OFTB

A JAIDE neurális architektúra eltér a hagyományos Transformer-alapú modellektől, mivel tisztán reverzibilis keretrendszert használ. A rendszer két alapvető primitívre épül: a Reversible Scatter Flow (RSF) az állapottranszformációkhoz és az Orthogonal Fractal Transform Block (OFTB) a dimenziókeveréshez. Ezek az összetevők együttesen lehetővé teszik a rétegek számához viszonyított $O(1)$ memóriakomplexitású képzést, mivel a köztes aktivációkat nem kell tárolni a visszamenőleges menethez.

### Visszafordítható szórásos áramlás (RSF)

Az RSF egy "ontológiailag puritán" architektúra, amely az önmegfigyelést, az MLP-ket és a LayerNorm-ot egyetlen invertálható affin csatolási primitívvel helyettesíti A korábbi generatív áramlatokkal ellentétben, mint a RealNVP vagy a Glow, az RSF a diszkriminatív LLM feladatokra van optimalizálva azáltal, hogy egyszerű mátrix-vektor szorzásokat ($W \cdot x + b$) használ a csatolási rétegeken belül, nem pedig belső ResNet/MLP blokkokat

A rendszer magja a LayerCore struktúra, amely négy elsődleges súlytenzort tart fenn: s_weight, t_weight, s_bias és t_bias

### Forward és inverz műveletek

Az RSF architektúra a matematikai invertibilitás révén 100%-os információmegőrzést biztosít.

- Előre passz: A forwardOnCore-t használja a bemeneti állapotok affin csatolással történő átalakítására
- Inverz passz: Az inverseOnCore-t használja az előző állapotok rekonstruálására a visszafelé haladás során, lehetővé téve az $O(1)$ memóriaelőnyt

A megvalósítás részletei, a pheap-en keresztüli súlymegmaradás és a CoreRegistry, lásd

### Ortogonális fraktál transzformációs blokk (OFTB)

Az OFTB az architektúrán belül "keverőként" szolgál, felváltva a más modellekben megtalálható tanult permutációkat vagy drága figyelemmátrixokat. Egy determinisztikus "szórás" műveletet hajt végre, amely biztosítja az információáramlást minden dimenzióban.

### Pillangó keverő mechanizmus

Az OFTB egy pillangó stílusú műveletet használ (a kernelekben rsf_scatterként, vagy a Zig CPU implementációban forwardInPlace-ként implementálva) a vektor felének keverésére $1/\sqrt{2}$ fraktál skála használatával Ez olyan strukturális keverést biztosít, amely lehetővé teszi a globális kontextus modellezését az önfigyelés $O(N^2)$ költségei nélkül

OFTB keverési logika:

| Művelet | Matematikai forma | Kódegység |
| --- | --- | --- |
| Fraktálskála | $1/\sqrt{2} \approx 0.7071$ | OFTB.fractal_scale |
| Sum Component | $x_1 = x_1 + x_2 \cdot scale$ | OFTB.forwardInPlace |
| Difference Component | $x_2 = x_2 + x_{1_old} \cdot scale \cdot 0.5$ | OFTB.forwardInPlace |

A Lean 4 verifikációs specifikációit és a részletes pillangó-interleavinget lásd

A következő ábra azt szemlélteti, hogy a magas szintű neurális fogalmak hogyan illeszkednek a src/processor/ könyvtárban található konkrét kódegységekhez.

### O(1) Memória Visszamenőleges passz

Ennek az architektúrának a meghatározó jellemzője az "aktiválási memóriafal" megszüntetése A szabványos transzformátorokban a memória $O(L)$ a rétegek számával együtt nő, mivel az aktivációkat a gradiens számításhoz gyorsítótárba kell helyezni. A JAIDE RSF architektúrája az inverseOnCore módszerrel menet közben rekonstruálja az aktivációkat

### Memória összehasonlítás

| Metric | Transformer / Mamba | JAIDE (RSF + OFTB) |
| --- | --- | --- |
| Visszamenőleges memória | $O(L)$ (Lineáris rétegekkel) | $O(1)$ (Állandó) |
| Aktiválási tároló | Kötelező | Nem kötelező | Nem kötelező |
| Max rétegmélység | VRAM korlátozott (~100s) | Elméletileg korlátlan (10,000+) |

- MGT Tokenizer: Mielőtt az adatok belépnének az RSF/OFTB csővezetékbe, a morféma-vezérelt tokenizáló feldolgozza őket, amely a bemenetet gyökökre és toldalékokra bontja. Lásd
- SFD optimalizáló: Az RSF visszamenőleges menet által előállított gradienseket a sztochasztikus Fisher-diagonális optimalizáló használja fel. Lásd
- Formális ellenőrzés: A forwardOnCore és inverseOnCore műveletek bijektivitását formálisan a Lean 4 segítségével ellenőrizzük. lásd

## RSF: Megfordítható szórásos áramlás megvalósítása

A Reversible Scatter Flow (RSF) egy új, JAIDE-ban implementált neurális architektúra, amely a hagyományos komponenseket, mint az önfigyelem, az MLP-k és a LayerNorm egy matematikailag inverzibilis affin csatolási primitívvel helyettesíti Az RSF $O(1)$ memória komplexitást ér el a visszafelé haladás során az aktivációk kimenetből történő rekonstruálásával, kiküszöbölve a köztes állapotok tárolásának szükségességét

### Építészeti áttekintés

Az RSF az információ megőrzésének elvére épül. A hagyományos architektúrákkal ellentétben, amelyek az információt nem lineárisan pusztítják el (pl. ReLU), az RSF olyan kereszt-affin csatolási rétegeket használ, amelyek eleve bijektívek

### Alapvető összetevők

- LayerCore: Az RSF alapegysége, amely négy súlytenzort tartalmaz: s_weight, t_weight, s_bias és t_bias
- Affin csatolás: Egy osztott skála-transzlációs mechanizmus, ahol a bemenet egyik fele módosítja a másik felét
- Szórási mechanizmus: Az OFTB (Orthogonal Fractal Transform Block) segítségével megvalósított mechanizmus biztosítja a dimenziók közötti információáramlást tanult permutációk nélkül

### RSF rendszerarchitektúra

A következő ábra a magas szintű RSF-struktúra és a mögöttes kódegységek közötti kapcsolatot szemlélteti.

### A LayerCore és a súlyok

A LayerCore struktúra határozza meg egy RSF réteg megtanulható paramétereit. Kezeli a skálázáshoz ($s$) és a transzlációhoz ($t$) használt súlyokat, valamint az optimalizáláshoz szükséges gradienseket

| Tensor neve | Szerep | Cél |
| --- | --- | --- |
| s_weight | Scaling Weight | A kapcsolás multiplikatív tényezőjének megtanulása. |
| t_weight | Fordítási súly | A kapcsolás additív eltolásának megtanulása. |
| s_bias | Scaling Bias | A skálázási művelet előfeszítése. |
| t_bias | Fordítási torzítás | A fordítási művelet torzító kifejezése. |

Súlyaktiválás: Az exp(clip(-)) Mechanizmus A numerikus stabilitás biztosítása és a robbanó gradiensek elkerülése érdekében a skálázási tényezőt a következőképpen számítjuk ki: $y = \exp(\text{clip}(W \cdot x + b))$. A clip művelet a clip_min és a clip_max határai (alapértelmezett értékek: -5.0 és 5.0 között)

Források:   9

### Adatáramlás: Előre és inverz

Az RSF architektúra a ForwardOnCore és InverseOnCore függvényekre támaszkodik az adatok feldolgozásához. Mivel a transzformáció bijektív, az inverz lépés tökéletesen rekonstruálja a bemenetet a kimenetből

### Előre passzolás (ForwardOnCore)

1.   Szétválunk: Az $X$ bemenetet két részre osztjuk, $x_1$ és $x_2$.
2.   $x_1$ skálázása/fordítása: $y_1 = x_1 \odot \exp(\text{clip}(s_{súly} \cdot x_2 + s_{bias})) + (t_{súly} \cdot x_2 + t_{bias})$.
3.   Keresztkapcsolás: A módosított $y_1$-t ezután $x_2$ módosítására használjuk, hogy $y_2$-t kapjunk.
4.   Szétszóródni: Az rsf_scatter függvény (OFTB) a $y_1$ és $y_2$ értékeket $1/\sqrt{2}$ skálázási tényezővel keveri

### Inverz átjáró (InverseOnCore)

Az inverz lépés a műveleteket fordított sorrendben, fordított aritmetikával végzi (összeadás helyett kivonás, szorzás helyett osztás/negatív kicsinyítés) az eredeti bemenet rekonstruálása érdekében

Források:  9

### Tartósság és memóriakezelés

Az RSF egy speciális perzisztencia rendszert használ a több mint 10 000$-os rétegmodellekben lehetséges hatalmas számú paraméter kezelésére

### CoreRegistry és pheap

A CoreRegistry az összes LayerCore-példány központi kezelőközpontjaként működik. A pheap (Persistent Heap) rendszerrel együttműködve biztosítja a modellsúlyok hatékony mentését és betöltését

### SaveTransaction

Az adatintegritás biztosítására az ellenőrzőpontozás során az RSF a SaveTransactiont használja. Ez a mechanizmus a szerializálási folyamatot foglalja magába, biztosítva, hogy a MAGIC_HEADER (JAIDE40\x00) és a CRC32 ellenőrző összegek helyesen kerüljenek alkalmazásra a modellfájlban 17

### Modell szerializációs formátum

A modellfájlok a model_io.zig fájlban meghatározott struktúrával kerülnek mentésre:

1.   Mágikus fejléc: JAIDE40\x00
2.   Metaadatok: JSON-kódolt ModelMetadata, beleértve az rsf_layers, rsf_dim és mgt_vocab_size adatokat is
3.   Komponensadatok: LayerCore tenzorok és optimalizáló állapotok

### Hardveres gyorsítás

Az RSF az NVIDIA hardverekre (B200/B300) optimalizált a közvetlen Zig-to-CUDA/Futhark integráció révén

- Tűzött emlék: Accel_interface.zig-t használ a CPU és a GPU közötti aszinkron DMA átvitelhez
- Warp optimalizálás: Az alapértelmezett csoportméretek 256-ra vannak beállítva (8 CUDA warp) a Tensor Core kihasználtság maximalizálása érdekében
- IO-kötődésű kárenyhítés: Mivel az RSF nem rendelkezik a transzformátorok $O(N^2)$ figyelem mátrixával, elkerüli a memória sávszélességének gyakori szűk keresztmetszetét

Források:  5

## OFTB: Ortogonális fraktál transzformációs blokk

### "Nyitott adattár")

Devin

Utolsó indexálás: 2026. május 2. (

Menü

### OFTB: Ortogonális fraktál transzformációs blokk

Az OFTB (Orthogonal Fractal Transform Block) egy fix súlyú keverési mechanizmus a JAIDE architektúrán belül, amelynek célja a felosztott adatcsatornák közötti információcsere megkönnyítése. A tanult permutációk vagy az áramlásalapú modellekben jellemzően megtalálható véletlenszerű keverés helyettesítésére szolgál, determinisztikus, energiatakarékos "pillangó" keverést biztosítva.

### Cél és mechanizmus

Az OFTB a fraktál pillangó transzformáció elve alapján működik. Elsődleges szerepe a Reversible Scatter Flow (RSF) csatolási rétegekkel való átlapolás, amely biztosítja, hogy a tenzor egyik feléből származó jellemzők a következő transzformációs szakasz előtt keveredjenek a másik felébe. Ez a keveredés alapvető fontosságú a csatoláson alapuló architektúrák kifejezőképessége szempontjából, mivel lehetővé teszi, hogy minden dimenzió végül minden más dimenzióra hatással legyen

A legfontosabb jellemzők:

- Ortogonalitás: A transzformációt úgy tervezték, hogy közel ortogonális legyen, megőrizve a rejtett állapotok normáját, hogy megakadályozza az eltűnő vagy robbanó aktivációkat a mély egymásra helyezés során.
- Fraktál skálázás: Egy állandó, $1/\sqrt{2}$ (kb. 0.70710678) skálázási tényezőt használ, hogy a keverék változatosságát fenntartsa
- Helyszíni működés: A memóriaterhelés minimalizálása érdekében mind az előre-, mind a hátrafelé irányuló átmenetek helyközi pufferműveletként vannak végrehajtva 41

### A végrehajtás részletei

Az oftb.zig-ben található OFTB struktúra kezeli a keverési logikát. A bemeneti tenzort két félre (x1 és x2) osztja a megadott dim dimenzió alapján

### Előre passz (keverés)

Az előre transzformáció egy pillangószerű struktúrát követ, ahol x1 az x2 skálázott változatával frissül, majd x2 az x1 eredeti értékeivel frissül.

1.   Puffer Eredeti x1: Az első fele egy ideiglenes mix_bufba másolódik
2.   X1 frissítése: $x_1 = x_1 + (x_2 \szor 0.70710678)$
3.   X2 frissítése: $x_2 = x_2 + (eredeti_x_1 \szor 0.70710678 \szor 0.5)$

### Visszafelé haladva (gradiens terjedés)

A visszafelé történő átmenet megfordítja a logikát, hogy a gradienseket (g1, g2) helyesen terjessze. Hasonló puffer-alapú megközelítést használ annak biztosítására, hogy a gradiens áramlása megfeleljen a keverési művelet matematikai inverzének

### Adatáramlás és kód leképezés

A következő ábra azt szemlélteti, hogy az OFTB logika hogyan illeszkedik a Zig implementációhoz és az ebből eredő adattranszformációkhoz.

OFTB adatáramlás és entitás leképezés

### Formális ellenőrzés

Az OFTB megvalósítása mögött egy formális specifikáció áll a Lean 4-ben. Ez biztosítja, hogy a fixpontos aritmetika és a keverési logika megfeleljen a szükséges matematikai tulajdonságoknak, különösen az előre és az inverz műveletek azonosságának elméleti végtelen pontosságú kontextusban.

A Lean 4 specifikáció meghatározza:

- Fixpontos aritmetika: Egyedi FP struktúra $10^8$-os skálával a Zig implementáció lebegőpontos viselkedésének modellezésére
- Állandók: fractalScale (70710678) és halfFractalScale (35355339) a Zig fractal_scale és a fractal_scale 0.5 értékeknek megfelelően vannak definiálva
- Vektorműveletek: a zipWithFP és a mapFP a fixpontos számok listáira történő transzformáció meghatározására szolgálnak

### Építészeti integráció

A szélesebb körű RSF (Reversible Scatter Flow) architektúrában az OFTB a "Scatter" mechanizmusként működik. Míg a LayerCore a tanult affin transzformációkat kezeli, az OFTB biztosítja, hogy az állapottér partíciói folyamatosan keveredjenek.

Rendszerarchitektúra integráció

### Műszaki korlátok

- Puffer mérete: Mix_buf 16,384 elemű fix méretű stack puffert használ Ha a dimenzió fele meghaladja ezt a méretet, a függvény a keverés végrehajtása nélkül tér vissza
- Dimenzionalitás: A bemeneti x tenzornak legalább dim 2 hosszúságúnak kell lennie, hogy a kétirányú felosztás lehetővé tegye a kétirányú felosztást

Elutasíthatod

Frissítse ezt a wikit

Ez a wiki nemrégiben frissült. Kérjük, várjon 7 napot az újbóli frissítéshez.

### Ezen az oldalon

## MGT Tokenizer: Morféma-vezérelt tokenizálás

A morféma-vezérelt tokenizáló (MGT) egy speciális tokenizáló rendszer, amelyet arra terveztek, hogy a természetes nyelvet strukturálisan értelmes egységekre bontja. A standard Byte-Pair Encoding (BPE) rendszerrel ellentétben, amely kizárólag a gyakoriságra támaszkodik, az MGT nyelvészeti heurisztikákat tartalmaz az előtagokra, utótagokra és gyökökre vonatkozóan, különösen az agglutinatív jellemzőkhöz optimalizálva. A nyers szöveg és az alszekvencia-index (SSI) közötti elsődleges interfészként szolgál.

### 1. Rendszerarchitektúra

Az MGT rendszer kétirányú leképezést végez a karakterláncok és a numerikus azonosítók között, miközben speciális hash-térképeket tart fenn a morfológiai komponensek és a szekvenciaindexálásban használt horgonyzó tokenek számára.

### Tokenizer adatáramlás: Természetes nyelvből kódtérbe

Ez az ábra azt szemlélteti, hogy az MGT struktúra hogyan dolgozza fel a bemeneti szöveget az SSI és a Tensor rendszerekkel kompatibilis tokenfolyamokká.

### 2. Morfológiai bontás

Az MGT megkülönbözteti magát a morfémák explicit azonosításával. Ezt az inicializálás során az initMorphemes segítségével kezeljük, amely a belső hash-térképeket feltölti a közös nyelvi konstrukciókkal.

### 2.1 Előtagok és utótagok kezelése

A tokenizáló előtag- és utótag-térképeket tart fenn, hogy az összetett szavak alkotóelemeire való bontását rangsorolja.

| Component | Map Type | Példák (kódból) |
| --- | --- | --- |
| Előtagok | std.StringHashMap(u32) | "un", "re", "pre", "meg", "vissza", "legesleg" |
| Utótagok | std.StringHashMap(u32) | "ing", "tion", "ság", "ban", "atlan", "nként" |

### 2.2 horgony zseton

A horgonyzó tokenek olyan speciális szókincselemek, amelyeket az SSI a szekvencia keresés stabil belépési pontjainak létrehozására használ.

- A horgonyok az MGT.anchors-ban vannak tárolva, mint egy StringHashMap(u64)
- Az MGT.init során ezek a token_to_id leképezéssel kerülnek kereszthivatkozásra

### 3. Szókincs és BPE integráció

Az MGT hibrid megközelítést alkalmaz, amely a speciális tokenek rögzített szókincsét kombinálja a tanult BPE-összevonásokkal.

### Különleges zsetonok

Az MGT az első négy azonosítót a vezérlési szekvenciák számára tartja fenn:

- [PAD] (0): Padding
- [UNK] (1): Ismeretlen token
- [BOS] (2): A sorozat kezdete
- [EOS] (3): Sorozat vége

### BPE Merge Logic

A BPEMerge struktúra határozza meg a prioritást és az eredményül kapott token azonosítót az alszavas egységek összevonásához:

const BPEMerge = struct { token_id: u32, priority: u32,};

### 4. SSI integráció és szekvenciaindexálás

Miután a szöveget egy []u32 tömbbe tokenizáltuk, az alszekvencia-indexen (SSI) belül indexálásra kerül. Az SSI egy háromágú struktúrát használ, ahol minden egyes csomópont szegmensadatokat tartalmaz.

### SSI-csomópontok szerkezete

Az SSI a szegmenseket egy fába rendezi, amelynek fix bucket_width értéke 6 (csomópontonként 64 gyermek).

### Az SSI legfontosabb funkciói

- SSI.computeAnchorHash(tokens, position): A gyors visszakeresés megkönnyítése érdekében 64 bites hash-t generál a szekvencia pozíciójának és a token azonosítóinak kombinálásával
- SSI.insertIntoLeaf(...): Hozzáad egy tokenizált szegmenst az indexhez, a hash ütközések kezelése egy összekapcsolt listán keresztül (CollisionNode)
- SSI.refreshHash(node): Újra kiszámítja egy csomópont Merkle-stílusú hash-jét a gyermekei vagy szegmensei alapján, biztosítva az adatok integritását

### 5. Memóriakezelés

Az MGT rendszert úgy tervezték, hogy allokátor-agnosztikus legyen, és támogassa a különböző JAIDE memóriakezelőket.

- Kiosztott karakterláncok: Az MGT struct egy ArrayList([]u8) listában követi az összes dinamikusan allokált karakterláncot, hogy a deinit során a tisztítást biztosítsa
- Allokátor támogatás: Speciális inicializátorokat tartalmaz a JAIDE egyéni allokátoraihoz:
- initWithArena: ArenaAllocator: A core_memory.ArenaAllocator esetében
- initWithPool: PoolAllocator esetében
- initWithBuddy: BuddyAllocator esetén

## Következtetési csővezeték: SSI, Ranker és API-kiszolgáló

A JAIDE következtetési csővezeték a nyers HTTP-kéréseket rangsorolt, tokenizált kimenetekké alakítja át három elsődleges alrendszer: a következtetési kiszolgáló, az alszekvencia-index (SSI) és a rangsoroló (Ranker) összehangolásával. Ez a csővezeték nagy teljesítményű kötegelt feldolgozásra és valós idejű streamingre lett tervezve, az n-gram elemzés és a Locality-Sensitive Hashing (LSH) segítségével a modell indexelt tudásbázisából releváns szekvenciák kinyerésére és pontozására.

### A csővezeték áttekintése

Egy következtetési kérelem életciklusa ezt az utat követi:

1.   Lenyelés: Az InferenceServer fogadja a JSON kérést, érvényesíti az API kulcsokat, és érvényre juttatja a sebességkorlátokat
2.   Tokenizálás: A bemeneti szöveget az MGT (Morpheme-Guided Tokenizer) tokenazonosítók sorozatává dolgozza fel
3.   Visszakeresés: A rangsoroló azonosítja az n-grammokat a bemeneten belül, és a getSegment segítségével lekérdezi az SSI-t (Sub-Sequence Index) az előre kiszámított pontszámok és a horgony metaadatok lekérdezéséhez
4.   Újbóli pontozás: A rangsoroló egy többtényezős pontozási képletet alkalmaz - amely magában foglalja a sokféleséget, a horgonyok közelségét és a Jaccard hasonlóságot -, hogy végső relevancia pontszámot kapjon
5.   Válasz: A kiszolgáló a tokeneket és az opcionális beágyazásokat JSON válaszba csomagolja

### Következtetési architektúra: A kéréstől a rangsorolt eredményig

Az alábbi ábra az adatok áramlását mutatja be az elsődleges kódegységeken keresztül egyetlen következtetési lépés során.

### 3.1 Al-sorozatindex (SSI)

A Sub-Sequence Index (SSI) egy trie-alapú adatszerkezet, amelyet a token szegmensek hatékony tárolására és visszakeresésére használnak. A szegmensobjektumokat a hash-jeik alapján rendezi. A trie minden egyes csomópontja képes az ütközésláncok kezelésére, és fenntart egy hash-t a szerkezeti ellenőrzéshez Az index kritikus fontosságú a rangsoroló számára, hogy O(1) keresést végezzen az n-gram pontszámok között az újbóli pontozási fázisban.

A részletekért lásd

### 3.2 rangsoroló: Multi-Factor Re-Scoring Engine

A Ranker a csővezeték döntéshozó motorja. A RankerConfigben meghatározott tényezők súlyozott kombinációjával értékeli a szekvenciákat, mint például a DIVERSITY_WEIGHT (0,3) és a PROXIMITY_WEIGHT (0,3) LSH (Locality-Sensitive Hashing) paramétereket használ a változatos és releváns visszakeresés biztosítása érdekében A Ranker működhet standard kötegelt vagy streaming üzemmódban, 1024 token STREAMING_BUFFER_SIZE használatával

A részletekért lásd

### 3.3 Következtetési kiszolgáló API

A következtetési kiszolgáló biztosítja a JAIDE rendszer HTTP-interfészét. Konfigurálása a ServerConfig segítségével történik, amely olyan paramétereket határoz meg, mint a batch_size, a port és a rate_limit_per_minute. A szerver tartalmaz egy RateLimiter-t a visszaélések megakadályozására, és támogatja az állapotellenőrzéseket és a modell állapotjelentést. Az RSFLayer, az MGT, az SSI és a Ranker összekapcsolásával a szerver a szervező szerepét tölti be

A részletekért lásd

### Komponens kapcsolati térkép

Ez az ábra azt mutatja, hogyan inicializálódnak és hivatkoznak a rendszerösszetevők az InferenceServerben.

## Al-sorozat-index (SSI)

A Sub-Sequence Index (SSI) egy speciális trie-alapú adatszerkezet, amelyet a tokenizált szekvencia-szegmensek hatékony tárolására és visszakeresésére terveztek a következtetés során. A JAIDE következtetési csővezeték elsődleges indexelési rétegeként szolgál, lehetővé téve a rangsoroló számára, hogy a korábban látott vagy generált szegmenseket hash-alapú útválasztás és horgonypozíciók alapján lekérdezze.

### Építészeti áttekintés

Az SSI-t egy prefix-trieként valósítják meg, ahol a csomópontok az adatokat hash-vödrök alapján továbbítják. Olyan szegmensobjektumokat kezel, amelyek tokenszekvenciákat, azok eredeti pozícióit és pontozási metaadatokat foglalnak magukba.

### Alapvető összetevők

| Komponens | Leírás | Fájlhivatkozás |
| --- | --- | --- |
| SSI | A fő indexvezérlő, amely a trie rootot és az allokátort kezeli. | |
| Csomópont | Olyan háromágú csomópont, amely lehet ág (amely gyermekeket tartalmaz) vagy levél (amely szegmenseket tartalmaz). | |
| Szegmens | A tárolási egység, amely a token azonosítókat, a pozíciót és a horgonyzási hash-okat tartalmazza. | |
| CollisionNode | A leveleken belüli hash ütközések kezelésére használt linkelt listás csomópont. | |

### SSI adatszerkezet elrendezése

A következő ábra a trie-csomópontok és a tárolt szegmensek közötti kapcsolatot szemlélteti.

Hármas és szegmens hierarchia

### Adattárolás és zárolás

Az SSI determinisztikus hashing-mechanizmust használ a szegmensek továbbítására és a duplikációk felismerésére.

### Segment Hashing

A szegmenseket két különböző hash azonosítja:

1.   Token Hash: Kizárólag a token szekvenciából a hashTokens használatával számítják ki
2.   Full Hash: A csomópontok integritásának és egyediségének ellenőrzésére használt összetett hash, amely tartalmazza a pozíciót, a pontszámot, a horgony hash-t és a tokeneket

### Routing logika

A trie-n való átvezetést a bucketIndex határozza meg, amely egy 6 bites indexet von ki egy 64 bites pozícióértékből A trie fix bucket_width értéke 6, ami 64 gyermeket eredményez elágazási csomópontonként

Természetes nyelvből kódba történő entitás leképezés: Hashing Flow

### A végrehajtás részletei

### Csomópont életciklusa

A csomópontok egy adott magassággal vannak inicializálva. Ha a magasság > 0, a csomópont egy ág, és egy vödörnyi gyermekmutatót rendel hozzá A levélcsomópontok (magasság == 0) egyetlen szegmenst és egy opcionális collision_chain-t tárolnak a hash ütközések kezelésére

### Integritás és kitartás

Az SSI minden egyes csomópontra vonatkozóan gördülő hash-t tart fenn.

- Levélcsomópontok: A hash az elsődleges szegmens és az ütközéslánc összes szegmensének fullHash() összegzése
- Elágazási csomópontok: A hash az összes nem-null gyermek hash-jának felhalmozása

Ez a refreshHash segítségével indított rekurzív hash-mechanizmus lehetővé teszi az index állapotának O(log N) verifikációját.

### Ütközéskezelés

Ha több szegmens tartozik ugyanahhoz a levélcsomóponthoz, az SSI egy CollisionNode összekapcsolt listát használ.

- Az első szegmens közvetlenül a Node.szegmensben van tárolva
- Az ezt követő szegmensek az collision_chain-hez vannak csatolva

Szegmens beszúrási logika

### Interface a Ranker számára

Az SSI biztosítja a getSegment interfészt (és a hozzá tartozó traverzális logikát), amelyet a rangsoroló használ a jelölt szekvenciák újbóli pontozásához. A visszakeresési folyamat ugyanazt a bucketIndex logikát használja a lekérdezési pozíciónak megfelelő levélcsomópont megtalálásához, majd végigjárja az ütközésláncot, hogy megtalálja a kért kritériumoknak megfelelő szegmenseket.

### Kulcsállandók

- bucket_width: 6 (64-utas elágazás)
- max_height: 6 (Maximális trie mélység)
- tensor_width: 134 (Belső igazítási konstans)

## Rangsoroló: Multi-Factor Re-Scoring Engine

A rangsoroló a JAIDE LLM következtetési csővezeték utolsó szakasza. Elsődleges feladata a Sub-Sequence Index (SSI) által visszakeresett szekvenciajelöltek újbóli pontozása egy többtényezős heurisztikus motor segítségével A strukturális n-gramm-elemzést, a Locality Sensitive Hashing-et (LSH), a szemantikai sokféleséget és a lekérdezésen alapuló hasonlóságot (Jaccard) kombinálja a token szekvenciák végső relevanciájának meghatározásához

### Pontozási csővezeték architektúra

A Ranker struktúra kezeli a pontozáshoz szükséges állapotot, beleértve a csökkenő n-gram súlyokat és az LSH hash paramétereket A token szekvenciákkal ([]const u32) dolgozik, és közvetlenül az SSI-vel lép kölcsönhatásba az előre kiszámított szegmens pontszámok lekérdezése érdekében

### Adatáramlás: Token a végső pontszámig

A következő ábra azt szemlélteti, hogy a nyers tokenszekvencia hogyan alakul át normalizált relevanciapontszámmá.

Ranker Pipeline adatáramlás

### Többtényezős pontozás összetevői

A végső pontszám a RankerConfigben meghatározott különböző metrikák súlyozott összege

| Paraméter | Érték | Leírás |
| --- | --- | --- |
| BASE_SCORE_WEIGHT | 0.4 | Az SSI-ből származó nyers n-gram pontszámok súlya. |
| DIVERSITY_WEIGHT | 0.3 | A tokenek sokféleségének súlya (egyedi/összes token). |
| PROXIMITY_WEIGHT | 0.3 | Az SSI horgonyzási pontokhoz való közelség súlya. |
| OVERLAP_WEIGHT | 0.3 | A lekérdezéssel való közvetlen token átfedés súlya. |
| JACCARD_WEIGHT | 0.3 | Jaccard-hasonlóság súlya a lekérdezések újrarendezéséhez. |

### 1. N-gram analízis és súlycsökkenés

Az init során a rangsoroló az ngram_weights-ot 1/n csökkenési faktorral inicializálja Ez biztosítja, hogy a hosszabb, specifikusabb n-grammok nagyobb mértékben járuljanak hozzá a pontszámhoz, mint a rövid, gyakoriak

A scoreSequence-ben a motor a num_ngrams-ig végigmegy az összes n-grammon, kiszámítja a stableHash-t, és lekérdezi az SSI-t

### 2. Token sokszínűség

A computeTokenDiversity függvény kiszámítja az egyedi tokenek arányát a teljes szekvencia hosszához képest egy AutoHashMap segítségével Ez büntet az ismétlődő vagy degenerált modell kimenetekért

### 3. Horgonyzás közelsége

A rangsoroló azt méri, hogy a megadott tokenek milyen közel vannak az SSI-ben tárolt "horgonypontokhoz" Ez az anchorProximity-ben van megvalósítva

### 4. Újrarangsorolás lekérdezés alapján

Ha a scoreSequenceWithQuery segítségével egy konkrét lekérdezést adunk meg, akkor a rangsorolót alkalmazzuk:

- Jaccard hasonlóság: A tokenek és a lekérdezés közötti halmazelméleti átfedés
- Token átfedés: A megosztott tokenek közvetlen számlálása a maximális hosszal normalizálva

### LSH és Hashing megvalósítása

A Ranker két magszaporítót használ a belső LSH függvények különböző hash paramétereinek létrehozásához

- HASH_SEED_MULTIPLIER_A: 0x9e3779b97f4a7c15
- HASH_SEED_MULTIPLIER_B: 0x517cc1b727220a95

Ezeket az inicializálás során az lsh_hash_params feltöltésére használják, hogy biztosítsák a determinisztikus, de változatos hash-elést több hash függvényen keresztül

### A végrehajtás részletei: Streaming Buffer

A valós idejű következtetéshez a Ranker támogatja a streaming üzemmódot. Egy csúszó ablakot tart fenn a tokenekből, amelyet a következők határoznak meg:

- STREAMING_BUFFER_SIZE: 1024
- STREAMING_WINDOW_SIZE: 512

Ez lehetővé teszi a motor számára, hogy folyamatosan értékelje a szekvenciákat, ahogyan azokat az LLM generálja, anélkül, hogy a teljes előzményeket újra feldolgozná

### Formális verifikáció (Viper)

A Ranker memóriabiztonsági és pontozási invarianciáit a Viper formális verifikációs keretrendszer segítségével verifikáljuk a src/verification/viper/ranker.vpr fájlban

### Ellenőrzési predikátumok

- valid_ranker: Ngram_weights és lsh_hash_params helyes kiosztását és a belső számlálókkal való konzisztenciáját biztosítja
- Fixpontos tartomány: Meghatározza a bitpontos lebegőpontos/fixpontos aritmetika axiómáit, beleértve az fp_clamp és fp_is_nan ellenőrzéseket is
- StableHash Domain: Axiomatizálja az SSI keresésekhez használt stable_hash függvény determinisztikus természetét

## Következtetési kiszolgáló API

A JAIDE Inference Server nagy teljesítményű HTTP-interfész biztosítja a modellkövetkeztetésekhez, integrálva az alapvető neurális architektúrát (RSF), a tokenizálást (MGT) és a visszakeresési/rangsorolási rendszereket (SSI, Ranker). Támogatja a többszálú kérések kezelését, a sebességkorlátozást és a kötegelt feldolgozást az átviteli teljesítmény optimalizálása érdekében.

### Kiszolgáló architektúra és életciklus

A kiszolgáló az InferenceServer struktúrában van elhelyezve, amely az összes szükséges következtetési komponens és az alapul szolgáló hálózati aljzat életciklusát kezeli.

### Inicializálás és konfiguráció

A kiszolgáló konfigurálása a ServerConfig struktúrán keresztül történik, amely meghatározza a hálózati paramétereket, a biztonsági követelményeket és a modell útvonalakat.

| Paraméter | Típus | Alapértelmezett | Leírás |
| --- | --- | --- | --- |
| port | u16 | 8080 | A HTTP-kiszolgáló TCP-portja. |
| host | []const u8 | "127.0.0.0.1" | Kötési cím. |
| max_connections | u32 | 100 | Maximális egyidejű TCP-kapcsolatok. |
| batch_size | usize | 32 | Az RSF-motor következtetési tételeinek mérete. |
| require_api_key | bool | true | Engedélyezés engedélyezése: Bearer <key> ellenőrzését. |
| rate_limit_per_minute | u32 | 10 | Percenként engedélyezett kérések IP-nként. |

### Komponensek bekötése

A kiszolgáló az init során a következő komponenseket kapcsolja össze

1.   MGT (Morpheme-Guided Tokenizer): A nyers kérési szöveget tokenszekvenciákká alakítja át.
2.   SSI (alszekvencia-index): A korábbi szegmensek gyors visszakeresését biztosítja.
3.   Rangsoroló: A SSI jelöltjeit a lekérdezés hasonlósága alapján újraértékeli.
4.   RSF (Reversible Scatter Flow): A neurális mag, amely a tokenbeágyazásokon az előrehaladást végzi.

### Adatáramlás: Kérés-válasz

A következtetési csővezeték áthidalja a természetes nyelvi tér (JSON/HTTP) és a kód entitás tér (Tensorok/RSF rétegek) közötti szakadékot.

### Következtetési csővezeték diagram

A következő ábra azt szemlélteti, hogy egy bejövő HTTP-kérelem hogyan halad át a rendszerösszetevőkön.

### Kérelem- és válaszformátumok

A kiszolgáló JSON használatával kommunikál. Az InferenceRequest struktúra kezeli az elemzést, míg az InferenceResponse a szerializálást.

Kérelem séma:

{ "text": "The quick brown fox", "max_tokens": 50, "return_embeddings": true}

Válasz séma:

{ "tokenek": [102, 45, 299], "embeddings": [102, 45, 299], "embeddings": [102, 45, 299]: [0.12, -0.45, 0.88], "processing_time_ms": 12.45}

### Biztonság és forgalomirányítás

A kiszolgáló két elsődleges védelmi réteget valósít meg: API-kulcs-hitelesítés és egy csúszóablakos sebességkorlátozó.

### Rátakorlátozás végrehajtása

A RateLimiter egy std.StringHashMap-ot használ az IP-címek követésére. Minden bejegyzés egy RequestLogot tartalmaz egy mutex-védett ArrayList időbélyegekkel.

- Ablak: 60 másodperc
- Mechanizmus: A checkAndRecord függvény törli a lejárt időbélyegeket, és összehasonlítja a fennmaradó számot a max_requests értékkel.

### API kulcs hitelesítés

Ha a require_api_key engedélyezve van a ServerConfigban, a kiszolgáló Authorization: Bearer fejlécet. A kulcsok kezelése az api_keys hash-térképen keresztül történik az InferenceServer struktúrán belül.

### Komponens integráció részletei

A következő ábra a magas szintű rendszerösszetevőket a konkrét végrehajtási fájlokhoz és elsődleges adatstruktúrákhoz rendeli.

### Végrehajtási folyamat

1.   Fő bejegyzés: A src/inference_server_main.zig fájl elemzi a parancssori argumentumokat (pl. --port, --model), és feltölti a ServerConfig
2.   Kiszolgálói hurok: StreamServer inicializál egy net.StreamServer-t és belép egy elfogadási ciklusba [src/api/inference_server.zig:250-300] (a megadott részletben csonkolva): InferenceServer.start() inicializál egy net.StreamServer-t és belép egy elfogadási ciklusba [src/api/inference_server.zig:250-300].
3.   Menetes kezelés: Minden egyes kapcsolat külön szálban vagy egy szálkészleten keresztül kezelendő, hogy megakadályozza a fő átvételi ciklus blokkolását.
4.   Tenzorintegráció: Tensor objektummá [src/core/tensor.zig] konvertáljuk, mielőtt átadnánk az RSFLayer-nek a számításhoz.

## Optimalizáló: SFD és másodrendű képzés

A JAIDE optimalizáló keretrendszer nagy teljesítményű, másodrendű optimalizációs algoritmusokat biztosít, amelyeket a modern mélytanulási munkaterhelésekhez és a speciális hardverekhez terveztek Az elméleti görbületbecslés (Hessian/Fisher információ) és a gyakorlati, hardveresen gyorsított képzés közötti szakadékot hidalja át NVIDIA Blackwell (B200) architektúrákon

### Rendszerarchitektúra áttekintése

Az optimalizáló rendszer négy hierarchikus rétegre tagolódik, a nyers memóriakezeléstől az automatikus hiperparaméter-hangolásig.

1.   Tensor primitív réteg: Támogatja a vegyes pontosságot az FP64-től az FP4-ig, hardver-érzékeny memóriakezeléssel
2.   Optimalizáló réteg: Az olyan alapvető algoritmusok, mint az SFD (Stochastic Fisher Diagonal) és a SophiaSOAP, amelyek a görbületi információt adaptív tanulási arányokhoz használják fel
3.   Hardware Abstraction Layer (HAL): Kifejezetten az NVIDIA B200 GPU-kra optimalizált, a Tensor Memory (TMEM) és a kernel fúzióját kezeli
4.   Képzési segédprogramok: LRScheduler stratégiákat, MixedPrecisionTrainer koordinációt és BayesianOptimizer-t biztosít a tuninghoz

### Logikából kódba történő entitás leképezés

A következő diagram a magas szintű optimalizálási koncepciókat a kódbázisban található konkrét megvalósítási egységekhez rendeli.

Optimalizálás Entitás leképezés

### SFD algoritmus: Stochastic Fisher Diagonal

Az SFD (Stochastic Fisher Diagonal) a JAIDE elsődleges optimalizálója. Belső puffereket tart fenn a lendület, a sebesség és a Fisher-diagonális számára, hogy kiszámítsa a veszteségfelület geometriáját figyelembe vevő paraméterfrissítéseket Úgy tervezték, hogy gyorsabban konvergáljon, mint a standard elsőrendű optimalizátorok, mint például az Adam, egy Fisher információs mátrix (FIM) közelítéseken alapuló, paraméterenként adaptív tanulási sebességet használva

Kulcsfontosságú összetevők:

- Lendület/sebesség: A gradiensek és a négyzetes gradiensek mozgó átlagai
- Fisher Diagonal: Becsüli a görbületet a gradiens előfeltételezéséhez
- Hutchinson becslő: Hatékony Hessian diagonális közelítéshez használatos

A matematikai megvalósítás és az ütemezési stratégiák mélyebb megismeréséhez lásd

### B200 hardveroptimalizálás és vegyes pontosság

A JAIDE az NVIDIA B200 (Blackwell) architektúrára van optimalizálva. Ez kifinomult memória-összeállítással és alacsony pontosságú aritmetikával jár az átviteli sebesség maximalizálása érdekében.

Hardveres jellemzők:

- TMEM (Tensor Memory): A B200MemoryManager által kezelt 32 MB-os nagysebességű memória, amely a HBM-ből a tenzorokat a hozzáférési frekvencia alapján migrálja
- Magfúzió: A B200KernelOptimizer egyetlen fused_gemm_bias_act hívásba egyesíti a MatMul, Bias és Activation műveleteket a memória sávszélesség szűk keresztmetszeteinek csökkentése érdekében
- Vegyes precizitás: A MixedPrecisionTrainer és a DynamicLossScaler által kezelt FP4 és FP8 kvantálás natív támogatása a numerikus stabilitás fenntartása érdekében

Optimalizáló végrehajtási folyamata

A hardver-specifikus kernelek és a kvantálási logika részleteiért lásd a

## SFD algoritmus: Stochastic Fisher Diagonal

A Stochastic Fisher Diagonal (SFD) optimalizáló egy nagy teljesítményű másodrendű optimalizációs könyvtár, amelyet a modern mélytanulási feladatokhoz terveztek Az elméleti másodrendű módszerek és a gyakorlati hardveres gyorsított képzés közötti szakadékot hidalja át azáltal, hogy hatékony görbületbecslési technikákat biztosít, kifejezetten az NVIDIA B200 (Blackwell) architektúrákra optimalizálva

### SFD Core végrehajtás

Az SFD algoritmus a lendület, a sebesség és a Fisher Information Matrix diagonális közelítés kombinálásával paraméterenként adaptív tanulási sebességet valósít meg Minden paraméterhez belső puffereket tart fenn, hogy ezeket a mozgó átlagokat követni tudja

### Adatáramlás és frissítési logika

A frissítési folyamat minden egyes képzési lépésnél meghatározott sorrendet követ:

1.   Momentum frissítés: kiszámítja a gradiensek mozgó átlagát a béta1 segítségével 39
2.   Velocity Update: A négyzetes gradiensek mozgó átlagának kiszámítása béta2 használatával 39
3.   Fisher Diagonális korrekció: Összevonja a második pillanatokat a Fisher információ becsléseivel, hogy a tanulási ráta geometriai adaptációját biztosítsa
4.   Paraméter lépés: A véglegesen kiszámított frissítést alkalmazza a súlytenzorokra

### Algoritmus Entitás leképezés

A következő diagram a magas szintű optimalizálási koncepciókat az src/optimizer/sfd.zig fájlban található konkrét kódegységekhez rendeli hozzá.

Optimalizáló komponens architektúra

### Sztochasztikus Fisher-becslés

Az SFD algoritmus Hutchinson becslőt használ a Hessian diagonális közelítéshez és a Fisher információs mátrix (FIM) diagonális követéséhez. Ez lehetővé teszi az optimalizáló számára, hogy a veszteségfelület geometriáját a teljes Hess-féle $O(N^2)$ költség nélkül vegye figyelembe

### Kulcsszerkezetek és konfiguráció

Az optimalizáló az SFDConfig struktúrán keresztül konfigurálható:

| Paraméter | Típus | Leírás |
| --- | --- | --- |
| beta1 | f32 | Exponenciális bomlási sebesség az első impulzusra |
| beta2 | f32 | A második impulzus (sebesség) exponenciális bomlási rátája |
| eps | f32 | Állandó a numerikus stabilitás érdekében |
| learning_rate | f32 | A frissítések alaplépésmérete |
| fisher_max | f32 | A Fisher-diagonális értékek felső határa az instabilitás elkerülése érdekében |
| finite_diff_eps | f32 | Epsilon a másodrendű lépésekben történő véges differencia közelítéshez |

### SophiaSOAP és KFAC integráció

Az SFD-t gyakran használják a SophiaSOAP-pal együtt, egy fejlettebb optimalizálóval, amely a Sophia másodrendű megközelítését a Kronecker-faktorált közelítő görbület (KFAC) kombinálja

- KFACBlock: Kronecker faktorok kezelése réteges gradiens előfeltételezéshez
- Sajátérték-korrekció: Megakadályozza az eltérést a Fisher-diagonális értékek fisher_max segítségével történő korlátozásával
- Hutchinson becslő: FillRademachert használ véletlen vektorok generálására a sztochasztikus nyomvonalbecsléshez

Görbületbecslés adatáramlás

Források:  39

### Vegyes pontosság és kvantálás

Az SFD támogatja az ultra-alacsony pontosságú képzést, fp64-től fp4-ig terjedően

### Kvantálási logika

A quantizeValue függvény kezeli a pontosságok közötti konverziót:

- FP4: -8,0 és 7,0 közé szorítva, 0,5-re kerekítve
- FP8: -448,0 és 448,0 közé szorítva, a legközelebbi 1/16-ra kerekítve

A Tensor struktúra megkönnyíti ezeket a konverziókat a copyFromWithCast segítségével, amely a másolás során minden elemre kvantálást alkalmaz

### Tanulási arány ütemezés

Az LRScheduler több stratégiát is alkalmaz a tanulás_rátájának modulálására a képzés során

1.   Bemelegítés: A tanulási sebesség lineáris növekedése egy megadott warmup_steps értékig
2.   Cosine Annealing: A tanulási sebesség periodikus csökkentése
3.   Sophia-stílusú hessi redukció: Dinamikusan módosítja a tanulási sebességet a veszteségfelület mért görbülete alapján

Források:  53

### Formális ellenőrzés (Lean 4)

A precíziós logika és a bitszélesség definícióit a Lean 4-ben formálisan ellenőrzik a körkörös konzisztencia és a tartománybiztonság biztosítása érdekében

- Precíziós tartomány: Az olyan tételek, mint a bitWidth_pos igazolják, hogy minden meghatározott formátum pozitív bitszélességgel rendelkezik
- Visszautazás Azonosság: A roundtrip_all tétel bizonyítja, hogy egy pontosság természetes számmá való átalakítása és vissza egy azonossági művelet
- Kizárási bizonyítékok: Az olyan tételek, mint az fp4_ne_fp8, formálisan bizonyítják a pontossági típusok megkülönböztethetőségét

## B200 hardveroptimalizálás és vegyes pontosság

A JAIDE LLM rendszer speciális optimalizációkat tartalmaz az NVIDIA Blackwell (B200) architektúrákhoz, az ultraalacsony pontosságú képzésre (FP4/FP8) és a nagy hatékonyságú memóriakezelésre összpontosítva. Ezek az optimalizációk áthidalják az elméleti másodrendű optimalizálás (SFD) és a hardveresen felgyorsított gyakorlati képzés közötti szakadékot

### B200 Hardveres gyorsítás

A hardveres absztrakciós réteg kifejezetten a B200 32 MB-os tenzormemóriájához (TMEM) van hangolva. A rendszer többszintű memóriastratégiát alkalmaz a HBM sávszélesség szűk keresztmetszeteinek minimalizálása érdekében

### TMEM és magfúzió

A B200MemoryManager kezeli a tenzorok elosztását a HBM és a TMEM között a hozzáférési gyakoriság alapján A rezsiköltség további csökkentése érdekében a B200KernelOptimizer operátorfúziót hajt végre, több neurális műveletet egyesít egyetlen Blackwell-optimalizált hívásba

- fused_gemm_bias_act: A mátrixszorzás, az előfeszítéses összeadás és az aktiválás funkciókat egyetlen kernel végrehajtásába olvasztja
- Teljesítményfigyelés: A PerformanceMonitor a hardver-specifikus metrikákat követi, beleértve a tensor_core_util és az nvlink_bandwidth_util mérőszámokat az optimális átviteli teljesítmény biztosítása érdekében

### Hardver interfész adatáramlás

A következő ábra a Futhark/CUDA magas szintű interfészei és a mögöttes hardveres primitívek közötti kapcsolatot szemlélteti.

B200 hardver interfész leképezése

### Vegyes precíziós edzés

A JAIDE az FP64-től az FP4-ig terjedő pontossági tartományt támogatja A MixedPrecisionTrainer koordinálja a master FP32 súlyok használatát a kvantált "munka" súlyok mellett, amelyeket az előre- és visszafelé haladás során használnak

### Kvantálás és skálázás

A numerikus stabilitás ultraalacsony pontosság mellett történő fenntartása érdekében a rendszer két elsődleges mechanizmust alkalmaz:

1.   DynamicLossScaler: Beállítja a veszteségskálát a képzés során, hogy megakadályozza a gradiens alul- és túlcsordulását FP8/FP4 formátumokban
2.   SpectralNormalizer: Optimalizált lineáris algebrai implementációkat biztosít a spectralNorm műveletekhez a mély RSF rétegek képzésének stabilizálása érdekében

### Numerikus pontosságú formátumok

| Formátum | Használat | Precíziós típus |
| --- | --- | --- |
| FP32 | Fősúlyok, akkumulátorok | f32 |
| FP16 | Alapértelmezett gyorsító formátum | f16 |
| FP8/FP4 | Tensor Core műveletek | u8 / u4 (csomagolt) |

### Optimalizálás alrendszerek

Az optimalizáló réteg a görbületbecslésre összpontosít, hogy a veszteségfelület geometriáját tiszteletben tartó adaptív tanulási arányokat biztosítson

### SFD és másodrendű módszerek

A sztochasztikus Fisher-diagonális (SFD) optimalizáló három elsődleges puffert tart fenn:

- Lendület: A gradiensek mozgó átlaga
- Sebesség: Négyzetes meredekség mozgó átlaga
- Fisher Diagonal: Görbületi közelítés, amelyet paraméteres adaptív skálázáshoz használnak

Az SFDConfig olyan paramétereken keresztül szabályozza ezeket a frissítéseket, mint a beta1, beta2 és fisher_max

### Bayesi hiperparaméter-hangolás

A BayesianOptimizer automatizálja a hiperparaméter-keresést egy Gauss-folyamat modell segítségével A konfigurációs teret (tanulási ráták, lendület stb.) a célfüggvény minimalizálása érdekében mintavételezi, anélkül, hogy manuális rácskeresésre lenne szükség.

Optimalizáló entitás kapcsolat

### Futhark Kernel implementáció

Az RSF (Reversible Scatter Flow) alapvető matematikai műveletei Futhark kernelként vannak implementálva a GPU-kon keresztül történő nagy teljesítményű párhuzamos végrehajtás érdekében

### RSF előre és hátra passzok

- rsf_forward: Kiszámítja az affin csatolási transzformációt. A bemenetet két félre osztja, az egyik félből származtatott skálát és transzlációt alkalmazza a másikra, és az eredményeket összekapcsolja
- rsf_backward: A súlyok (grad_ws, grad_wt) és a torzítások (grad_sb, grad_tb) gradienseit egy menetben számítja ki
- rsf_scatter: A pillangó keverési mechanizmust valósítja meg 1/√2 skálázási tényező és index alapú permutációk segítségével

### SFD frissítő mag

Az sfd_update_half kernel végzi a tényleges súlyfrissítést a GPU-n, alkalmazva a lendület és a sebesség frissítését a súlymátrixokra

## Core Relational Engine (CRE) és Quantum Graph System (kvantumgráf rendszer)

A Core Relational Engine (CRE) a JAIDE rendszer kognitív szubsztrátja. A hagyományos LLM-ekkel ellentétben, amelyek kizárólag lineáris vektorbeágyazásokra támaszkodnak, a CRE egy nem-lineáris önhasonló információs reprezentációt (NSIR) használ, hogy az adatokat kvantum-korrelált entitások gráfjaként modellezze. A klasszikus gráfelméletet kvantummechanikai tulajdonságokkal integrálja a bizonytalanság, a jelentések szuperpozíciója és a fraktális önhasonlóság különböző információs sűrűségeken keresztüli ábrázolása érdekében.

### Rendszer áttekintése

A CRE kezeli az átmenetet a nyers tokenizált bemenetről a strukturált, kvázi korrelált reprezentációkba. Kettős nyelvi stratégiára épül: egy nagy teljesítményű Zig implementáció a futásidejű végrehajtáshoz és egy matematikailag szigorú Lean 4 specifikáció a gráfműveletek formális ellenőrzéséhez.

A következő ábra a CRE logikai összetevői és a kódbázisban való megvalósításuk közötti kapcsolatot szemlélteti:

CRE komponensek leképezése

### NSIR mag: Önhasonló relációs gráf

A SelfSimilarRelationalGraph a CRE elsődleges adatszerkezete. Ez tárolja a Node és Edge primitíveket, ahol minden csomópont tartalmaz egy Qubit állapotot (komplex amplitúdók $\alpha$ és $\beta$), és minden él EdgeQuality (pl. szuperpozíció, összefonódott, fraktál) szerint van kategorizálva. A gráf fenntart egy topology_hash-t - egy SHA-256 XOR felhalmozást -, hogy biztosítsa a determinisztikus állapotkövetést a módosítások során.

A részletekért lásd

### ESSO: Összefonódott sztochasztikus szimmetria optimalizáló

Az EntangledStochasticSymmetryOptimizer (ESSO) egy szimulált lágyítási motor, amelyet a gráf topológiájának optimalizálására terveztek. Egy OptimizationState-t használ a mozgások kiértékelésére olyan objektív függvények alapján, mint a quantumCoherenceObjective és a fractalDimensionObjective. Az ESSO azonosítja a SymmetryPattern csoportosításokat, és kezeli az összefonódási bomlást az optimalizálási folyamat során.

A részletekért lásd

### FNDS: Fraktálcsomópont adatszerkezet

Az FNDSManager hierarchikus adatátirányítást biztosít egy FractalTree-n keresztül. A SelfSimilarIndex és a dobozszámláló fraktáldimenzió-elemzés segítségével kezeli az adatokat a különböző FractalLevel szinteken keresztül. Ez a rendszer lehetővé teszi, hogy a CRE megőrizze a strukturális integritást az információsűrűség különböző skáláin, amelyet egy LRU gyorsítótár és egy CoalescedHashMap támogat a hatékony átjárás érdekében.

A részletekért lásd

### Kvantumlogika, időgráf és jelterjedés

Ez az alrendszer kezeli a gráf dinamikus és időbeli aspektusait. A RelationalQuantumLogic olyan kapukat (Hadamard, Pauli-X/Y/Z) valósít meg, amelyek a QuantumState-on működnek. A TemporalGraph követi a NodeVersion és EdgeVersion előzményeit, míg a signal_propagation kezeli az ActivationTrace-t, ahogy a jelek a relációs hálózaton keresztül áramlanak.

A részletekért lásd

### Reasoning Orchestrator és Chaos Core

A ReasoningOrchestrator a magas szintű kognitív ciklusokat irányítja, ReasoningPhase lépéseken keresztül haladva és egy ThoughtLevel hierarchiát használva. Kapcsolódik a ChaosCoreKernelhez, amely tartalomcímezhető tárolót és DataFlowAnalyzer képességeket biztosít a rendszer entrópiájának és a memóriablokkok állapotának kezeléséhez.

A részletekért lásd

### Adatáramlás és az alrendszerek kölcsönhatása

A CRE ezeket a komponenseket egy egységes csővezetékbe integrálja, ahol az információ kódolása, modulálása és mérése történik.

CRE belső csővezeték

| Fázis | Felelős modul | Kódalany | Művelet |
| --- | --- | --- | --- |
| Kódolás | nsir_core.zig | encodeInformation | A nyers adatokat csomópontokká és élekké konvertálja |
| Optimalizálás | esso_optimizer.zig | ESSO | A topológia finomítása szimulált lágyítással |
| Indexelés | fnds.zig | FNDSManager | Az adatok fraktálhierarchiákba való átirányítása |
| Propagáció | signal_propagation.zig | propagateSignal | Az aktivációt szétteríti a gráfban |
| Measurement | nsir_core.zig | measure | A Qubit-állapotokat diszkrét eredményekre bontja |

## NSIR mag: Önhasonló relációs gráf

A nem-lineáris önhasonló információreprezentáció (NSIR) mag biztosítja az alapvető adatstruktúrákat és formális specifikációkat a JAIDE LLM projekt keretében működő kognitív relációs motor (CRE) számára A klasszikus gráfelméletet kvantummechanikai tulajdonságokkal hidalja át, hogy az információt nem-lineáris, önhasonló formátumban reprezentálja

A rendszer kétnyelvű stratégiával valósul meg:

1.   Zig (src/core_relational/nsir_core.zig): Nagy teljesítményű futásidejű implementáció kézi memóriakezeléssel és tensorintegrációval
2.   Lean 4 (src/verification/lean4/nsir.lean): Formálisan ellenőrzött specifikáció, amely biztosítja a kvantumlogika és moduláció matematikai szigorát

### Grafikus primitívek

### Node és Qubit

A gráf minden információs entitás egy csomópont. A hagyományos csomópontoktól eltérően az NSIR csomópontok tartalmaznak egy Qubit-állapotot, amely az információ összeomlásának valószínűségét jelzi a következtetés során

- Qubit: A $a$ és $b$ komplex amplitúdók által meghatározott. Tartalmazza a normalizálás és a mérési valószínűségek ($P(0)$ és $P(1)$) kiszámításának módszereit
- Csomópont: Tartalmaz egy egyedi azonosítót, nyers adatbájtokat, egy Qubitot, egy fázisértéket és egy StringHashMapot tetszőleges metaadatokhoz

### Edge és EdgeQuality

A csomópontok közötti kapcsolatokat az Edge struktúra reprezentálja. Az éleket a "minőségük" jellemzi, ami azt határozza meg, hogy a jelek hogyan terjednek a gráfban

Az EdgeQuality enum öt állapotot határoz meg:

| Minőség | Leírás |
| --- | --- |
| szuperpozíció | A kapcsolat több potenciális állapotban létezik. |
| összefonódott | Az egyik csomópont állapota függ a másiktól. |
| koherens | Stabil, fokozatos kapcsolat. |
| összeomlott | Egy megoldott, klasszikus kapcsolat. |
| fraktál | önhasonló rekurzív kapcsolat. |

### SelfSimilarRelationalGraph architektúra

A SelfSimilarRelationalGraph az NSIR rendszer elsődleges tárolója. Kezeli a csomópontok és élek életciklusát, miközben egy globális kvantumregisztert és egy kriptográfiai topológiai hash-t tart fenn

### Topológia Hash (SHA-256 XOR felhalmozás)

A determinisztikus állapotkövetés és az adatok integritásának biztosítása érdekében a gráf fenntart egy topology_hash-t. Minden módosítás (csomópontok hozzáadása, élek eltávolítása vagy kvantumállapotok frissítése) updateTopologyHash-t indít el. Ez a függvény SHA-256-ot használ az egyes komponensek hash-eléséhez, és XOR segítségével halmozza őket, biztosítva, hogy a hash sorrendfüggetlen legyen

### Az összefonódás életciklusa

A grafikon a Bell-állapotok segítségével követi a több csomópontból álló korrelációkat. Az entangleNodes függvény TwoQubitState-et hoz létre két csomópont azonosítója között, hatékonyan összekapcsolva kvantumvalószínűségeiket

### Mérés és összeomlás

A measureNode funkció egy döntési vagy felismerési eseményt szimulál. A csomópont Qubit-állapota alapján kiszámítja az összeomlás valószínűségét, és a "mérés" után a qubitet alapállapotba (|0> vagy |1>) állítja vissza

### Információáramlás: Természetes nyelvtől a kódolt entitásig

Az alábbi ábra azt szemlélteti, hogy a természetes nyelvi információk hogyan kerülnek bevitelre és hogyan alakulnak át NSIR kódegységekké.

Információfelvételi folyamat

### Adatműveletek

### encodeInformation

Ez a funkció a nyers adatok belépési pontjaként szolgál. Új csomópontot hoz létre, inicializálja a Qubitját szuperpozíciós állapotban, és automatikusan összefüggő éleket hoz létre a meglévő csomópontokhoz a topológiai közelség vagy a metaadatok hasonlósága alapján

### Tensor exportálás/importálás

Az NSIR grafikon integrálódik a JAIDE tenzorrendszerbe (core_tensor).

- Export: A gráf állapota (súlyok, korrelációk és fraktáldimenziók) exportálható Tensorba az RSF vagy OFTB neurális rétegek általi feldolgozáshoz
- Import: A neurális optimalizálóból tanult súlyok újraimportálhatók az élsúlyok és a kvantum korrelációk beállításához

### Megvalósítási logikai diagram

Az alábbi ábra a SelfSimilarRelationalGraph belső logikáját és a memória- és kriptoalrendszerekkel való kölcsönhatását mutatja be.

NSIR logika és alrendszerek kölcsönhatása

### Formális ellenőrzés (Lean 4)

Az NSIR rendszer matematikai helyességét az nsir.lean programban ellenőrizhetjük.

- Komplex aritmetika: Kvantum amplitúdók összeadásának, szorzásának és nagyságrendi számításainak ellenőrzött megvalósítása
- Élminőségi invariánsok: Bizonyítékok, amelyek biztosítják, hogy az EdgeQuality transzformációk (Nat vagy String felé/onnan) injektívek és kimerítőek
- Modulációs csővezeték: Az nsir_modulation.lean fájl definiálja a fixpontos aritmetikát (FP), amelyet a gráf átszelése során az információ skálázására, a modulációs faktorok asszociativitásának és disztributivitásának bizonyítására használnak

## ESSO: Összefonódott sztochasztikus szimmetria optimalizáló

Az Entangled Stochastic Symmetry Optimizer (ESSO) egy nagy teljesítményű optimalizáló motor, amelyet arra terveztek, hogy önszimiláris relációs gráfok komplex, nem konvex energiatáján navigáljon. A szimulált lágyítás, a kvantumlogika és a fraktálgeometria kombinációja, hogy globális minimumokat találjon ott, ahol a hagyományos gradiens ereszkedési módszerek a durva topológia miatt kudarcot vallanak

### Rendszerarchitektúra

Az ESSO négy elméleti terület metszéspontjában működik: Szimulált csillapítás a globális kereséshez, kvantummechanika a csomóponti állapotok reprezentálásához (Qubits), gráfelmélet a strukturális optimalizáláshoz, és fraktálgeometria az önhasonló minták fenntartásához

### Kód Entitás tér leképezése

A következő ábra a koncepcionális optimalizálási hurkot a kódbázisban található konkrét Zig-struktúrákhoz és -függvényekhez kapcsolja.

Optimalizálási logika és kód leképezése

### Optimalizálási állapot és motor

Az EntangledStochasticSymmetryOptimizer az elsődleges belépési pont Kezeli a hűtési ütemtervet, az iterációs korlátokat és a mag optimalizálási hurkot.

### Főbb összetevők

- OptimizationState: Egy SelfSimilarRelationalGraph-ot csomagol be, és tartalmaz egy entanglement_map-et (NodePairKey használatával) a történelmi korrelációk követésére
- UndoLog: Biztosítja a szigorú határokat az aktuális és a javasolt állapotok között, lehetővé téve a motor számára, hogy visszavegye az elutasított mozgásokat
- ObjectiveFunction: Fn (const OptimizationState) f64 típusú függvénymutató, amelyet az energiatájkép meghatározására használnak

### Hűtés és újramelegítés

A motor adaptív hűtési ütemtervet használ. Bár DEFAULT_INITIAL_TEMP (100,0) és DEFAULT_COOLING_RATE (0,95) értékkel indul, ha a rendszer túl sokáig egy helyi minimumon ragad, akkor újra felmelegedési mechanizmust indíthat el, ami ténylegesen megnöveli a hőmérsékletet, hogy kikerüljön a medencéből.

### Szimmetria észlelés és transzformáció

Az ESSO egyedülálló tulajdonsága, hogy képes felismerni és kihasználni a szerkezeti szimmetriákat (forgások, tükrözések, transzlációk), hogy nagyméretű "kvantumugrásokat" végezzen a keresési térben

### Szimmetria típusok

A SymmetryGroup enum határozza meg a támogatott geometriai transzformációkat:

- identitás, tükrözés, rotation_90, rotation_180, rotation_270, fordítás és custom_rotation

### Átalakulás végrehajtása

A SymmetryTransform struktúra ezeket a csoportokat alkalmazza a csomóponti koordinátákra és a kvantumfázisokra. Affin belső struktúrát használ a skálázás és a transzláció kezelésére

| Szimmetriacsoport | Sorrend | Szög (rad) | Megvalósítási logika |
| --- | --- | --- | --- |
| rotation_90 | 4 | $\pi/2$ | x = origo_x - dy, y = origo_y + dx |
| reflexió | 2 | 0.0 | Használja a cos(2θ) és sin(2θ) paramétereket |
| rotation_180 | 2 | $\pi$ | x = origo_x - dx, y = origo_y - dy |

### Az optimalizálási hurok: Mozgástípusok

Az ESSO hét különböző mozgástípuson keresztül vizsgálja a megoldási teret. Ezek a mozgások a gráf topológiáját, az élek súlyait vagy a csomópontok belső kvantumállapotát zavarják.

### Kategóriák mozgatása

1.   Peremsúly-zavarás: A meglévő Edge objektumok súlyának beállítása.
2.   Topológia mutáció: Csomópontok közötti élkapcsolatok hozzáadása vagy eltávolítása.
3.   Kvantum fáziseltolódás: Módosítja a csomópont kvantumállapotának fázisát.
4.   Összefonódás-beállítás: Frissíti az entanglement_mapet a korrelációk erősítése vagy lebontása érdekében.
5.   Szimmetriaugrás: SzimmetriaTranszformációt alkalmaz egy csomópontcsoportra.
6.   Fraktáldimenziós perturbáció: Módosítja a csomópontok fraktál_dimenzióját az önhasonló növekedés ösztönzése érdekében
7.   Qubit forgás: Egy Qubit komplex amplitúdójának elforgatását végzi el.

### Metropolis-Hastings átvétele

A mozgásokat az energia delta ($\Delta E$) és az aktuális hőmérséklet ($T$) alapján fogadjuk el: $$P(\text{elfogadás}) = \exp(-\Delta E / T)$$$ Ez lehetővé teszi a motor számára, hogy időnként "rosszabb" mozgásokat is elfogadjon, hogy elkerülje a lokális optimumokat

### Összefonódás és bomlás

Az ESSO hosszú távú korrelációkat modellez egy összefonódási térképen keresztül.

### Az összefonódás életciklusa

1.   Teremtés: Ha két csomópont gyakran fordul elő együtt a sikeres mozgások során, akkor az entanglement_map-ben létrejön egy EntanglementInfo bejegyzés
2.   Befolyás: SzimmetriaTranszformáció során az összefonódott csomópontok nagyobb valószínűséggel kerülnek egymáshoz.
3.   Bomlás: Az idő múlásával, ha a korreláció nem vezet energiacsökkenéshez, az összefonódás értéke csökken, ami végül a térképről való eltávolításához vezet.

### Adatáramlás: Optimalizálási ciklus

Az alábbi ábra szemlélteti az adatáramlást a kezdeti grafikontól a sztochasztikus motoron keresztül a végső optimalizált eredményig.

ESSO adatáramlás

## FNDS: Fraktálcsomópont adatszerkezet

A Fractal Node Data Structure (FNDS) egy speciális hierarchikus adatkezelő rendszer a JAIDE-n belül, amelyet önhasonló relációs modellek kezelésére terveztek. A szabványos sík gráfokkal ellentétben az FNDS rekurzív rétegekbe szervezi az adatokat, ahol a csomópontok diszkrét adatpontokat és alstruktúrák belépési pontjait is jelentik Ez az architektúra a fraktális dimenzióelemzésre, a több skálájú mintaillesztésre és a nagy teljesítményű hierarchikus útválasztásra optimalizált

### Központi architektúra és adatáramlás

Az FNDS-rendszer háromszintű hierarchiára épül:

1.   FNDSManager: FractalTree és SelfSimilarIndex példányokat kezelő legfelső szintű orchestrator
2.   FractalTree: FractalLevel szeletekre tagolt teljes hierarchikus adathalmazt reprezentáló függőleges tároló
3.   FractalLevel: FractalNodeData és FractalEdgeData elsődleges tárolására szolgáló vízszintes szelet egy adott mélységben

### Rendszerentitás-leképezés

A következő diagram a magas szintű fraktál fogalmakat a kódbázisban található implementációs entitásokhoz rendeli.

### FNDSManager és globális útválasztás

Az FNDSManager az összes fraktálszerkezet központi nyilvántartója. Egy StringHashMap-ot használ a több fa és az indexek egyedi azonosítókkal történő követésére

Kulcsfunkciók:

- init(allocator): A menedzser inicializálása, beleértve a globális LRUCache-t és a statisztikakövetőt is
- createTree(branching_factor, max_depth): Egyedi 32 bájtos tree_id-t generál és inicializál egy új FractalTree-t
- searchInTree(tree_id, node_id): Kétlépcsős keresési folyamat. Először lekérdezi az LRUCache-t egy összetett kulcs (buildCacheKey) segítségével; hiba esetén rekurzív keresést végez a célfa szintjein 96

Adatáramlás: Csomópont beszúrása

### FractalTree és FractalLevel

A FractalTree a csomópontokat méretarányuk és elágazási tényezőjük alapján rendezi. A szerkezeti integritást automatikus kiegyensúlyozással biztosítja

### FractalNodeData

A fa minden egyes csomópontját a FractalNodeData képviseli, amely a következőket tartalmazza:

- id és adatok: A nyers tartalom
- fractal_signature: 32 bájtos SHA-256 hash, amely biztosítja az adatok integritását és egyediségét 81
- mérleg és súly: A fraktálszámításokhoz használt matematikai paraméterek

### FractalLevel és dimenzióelemzés

A FractalLevel a hierarchia egy adott szemcseméretét képviseli. Tartalmaz egy calculateFractalDimension metódust, amely egy dobozszámláló algoritmust valósít meg az adott szintű adathalmaz komplexitásának becslésére 89

| Jellemző | Megvalósítás | Cél |
| --- | --- | --- |
| Tárolás | CoalescedHashMap | Hatékony tárolás nagy ütközéses forgatókönyvekhez |
| Integritás | Sha256 | Minden csomóponthoz fraktál aláírást generál |
| Routing | Wyhash | A gyermek elhelyezését a computeChildIndex segítségével határozza meg |
| Traversal | Rekurzív | Támogatja a Preorder, Postorder és Level-order sorrendet |

### SelfSimilarIndex és mintaillesztés

A SelfSimilarIndex egy mintaalapú keresési mechanizmust biztosít, amely független a fizikai fa struktúrától A karakterlánc-alapú mintákat konkrét PatternLocation koordinátákhoz (Tree ID, Level, Node ID) rendeli

Fuzzy Matching Logic: Amikor egy mintát lekérdeznek, az index azonosítja a hasonló fraktáljellemzőkkel rendelkező klasztereket, lehetővé téve a rendszer számára, hogy rokon fogalmakat találjon még akkor is, ha a pontos azonosítók különböznek

### Memóriakezelés és statisztikák

Az FNDS szigorú kézi memóriafegyelmet követ az std.mem.Allocator interfész használatával. Minden fontosabb struktúra (FractalNodeData, FractalTree, FNDSManager) implementálja az init, deinit és clone mintákat

Az FNDSStatistics struktúra a rendszer állapotát követi nyomon:

- Cache teljesítmény: cache_hits, cache_misses és cache_hit_ratio
- Szerkezeti állapot: átlagos_famélység és összes_csomópontok_fákon_keresztüli_mélysége
- Memóriahasználat: A memory_used explicit nyomon követése az összes allokált fraktál komponensben

## Kvantumlogika, időgráf és jelterjedés

Ez a modul határozza meg a Core Relational Engine (CRE) számítási alrendszerét. Egy kvantum-ihlette logikai rendszert valósít meg a relációs műveletekhez, egy időbeli gráfstruktúrát, amely a csomópontok állapotainak és élek topológiáinak verziószámozott történetét tartja fenn, valamint egy jelterjedési motort, amely hullámszerű aktiválásokat szimulál a relációs hálózaton keresztül.

### 1. Kvantum logikai rendszer

A quantum_logic modul biztosítja a kvantumállapotok relációs gráfon belüli ábrázolásához és manipulálásához szükséges primitíveket. A szabványos Boole logikától eltérően a JAIDE a QuantumState-t használja a csomópontok értékeinek amplitúdók szuperpozíciójaként való ábrázolására.

### 1.1. Logikai kapuk és műveletek

A LogicGate enum definiálja a szabványos kvantumkapukat (Hadamard, Pauli-X/Y/Z) a gráf-alapú következtetéshez használt speciális relációs kapuk mellett.

| Kapu | Típus | Qubits | Leírás |
| --- | --- | --- | --- |
| HADAMARD | Single | 1 | Szuperpozíciót hoz létre. |
| RELATIONAL_AND | Multi | 2 | Két csomópontot logikai ÉS kapcsolattal kapcsol össze. |
| RELATIONAL_NOT | Single | 1 | Egy csomópont amplitúdó/fázisának inverziója. |
| FRACTAL_TRANSFORM | Single | 1 | Önhasonló skálázást alkalmaz a kvantumállapotra. |

### 1.2. QuantumState megvalósítás

A QuantumState struktúra kezeli a komplex amplitúdókat és az összefonódási fokokat. Tartalmazza a normalizálás, a valószínűségszámítás és az állapotkombináció módszereit.

- prob0() / prob1(): Kiszámítja a $|0\rangle$ vagy $|1\rangle$ bázisállapotokba való összeomlás valószínűségét
- normalize(): Biztosítja, hogy a teljes nagyság $\sqrt{|a|^2 + |b|^2}$ egyenlő legyen 1.0-val
- RelationalQuantumLogic: LogicGate műveletek QuantumState példányokra történő alkalmazásához magas szintű interfész

### 2. Időbeli gráfszerkezet

A temporal_graph modul kibővíti az nsir_core gráfot azzal, hogy minden csomóponthoz és élhez idődimenziót ad hozzá. Ez lehetővé teszi a rendszer számára, hogy a tudásgráf történeti állapotain keresztülhaladjon, és időbeli következtetéseket végezzen.

### 2.1. Verziókezelő rendszer

Egy csomópont vagy él minden módosítása új verziót hoz létre ahelyett, hogy felülírná a meglévő adatokat.

- NodeVersion: Egy adott időbélyegnél tárol egy QuantumState és egy StringHashMap tulajdonságot
- EdgeVersion: EdgeQuality (pl. összefonódott, összeomlott) egy kapcsolat súlyát és minőségét tárolja egy adott időpontban

### 2.2. Időbeli entitások

A csomópontok és élek változatgyűjteményként vannak ábrázolva, időbélyegző szerint rendezve.

| Entity | Core Data | Version Container |
| --- | --- | --- |
| TemporalNode | node_id | ArrayList(NodeVersion) |
| TemporalEdge | EdgeKey (forrás/cél) | ArrayList(EdgeVersion) |

### 2.3. Formális ellenőrzés

A temporális gráf állapotkezelését a Lean 4-ben formálisan ellenőrizzük, biztosítva, hogy az olyan tulajdonságok, mint az EdgeQuality string konverziók injektívek legyenek, és hogy a QuantumState klónok megőrizzék az összes fizikai tulajdonságot.

### 3. Jelterjedési motor

A signal_propagation modul azt szimulálja, hogy az információ (jelek) hogyan terjednek a relációs gráfban. Ezt a mechanizmust a releváns részgráfok azonosítására és a ReasoningOrchestrator aktiválásának kiváltására használjuk.

### 3.1. Jelállapot és aktiválás

A SignalState egy hullámszerű csomagot reprezentál amplitúdóval, fázissal és frekvenciával. Amikor egy jel elér egy csomópontot, az ActivationTrace-ben rögzítésre kerül.

- SignalState: A terjedő hullám fizikai tulajdonságait határozza meg
- ActivationTrace: Fenntartja egy adott csomóponton áthaladó jelek előzményeit, az átlagos_amplitúdó és az aktiválás_számának kiszámításához használatos

### 3.2. Propagációs logika

A SignalPropagationEngine kezeli a globális szimulációs állapotot.

1.   initiateSignal: A forráscsomópontba egy kezdeti SignalState-ot injektál
2.   propagateStep: A gráfon végigmegy, és az EdgeQuality és a súly alapján jeleket mozgat az élek között
3.   kombinálni: Amikor több jel eléri a csomópontot, interferencia-szerű logika segítségével egyetlen állapottá kombinálódnak

### 4. Építészeti diagramok

### 4.1. Adatáramlás: Jel az időállapotba

Ez az ábra azt mutatja, hogy egy jel aktiválása végül egy új verziójú állapotot eredményez az időbeli gráfban.

### 4.2. Kódex entitás leképezés

A koncepcionális logika és a Zig implementációs fájlok közötti leképezés.

## Reasoning Orchestrator és Chaos Core

A Reasoning Orchestrator és a Chaos Core alkotja a JAIDE rendszer magas szintű kognitív és tároláskezelő rétegeit. Az Orchestrator az ESSO (Entangled Stochastic Symmetry Optimizer) különböző absztrakciós fázisokon keresztül történő vezérlésével többszintű érvelési hurkokat kezel, míg a Chaos Core tartalomcímezhető tároló (CAS) alapot biztosít entrópiatudatos adatkezeléssel és folyamelemzéssel.

### 1. Reasoning Orchestrator

A ReasoningOrchestrator felelős a SelfSimilarRelationalGraphon belüli "gondolatok" életciklusának kezeléséért Koordinál a relációs gráf, az ESSO optimalizáló és a Chaos Core között a gráf topológiájának finomítása és a szimmetriaminták felfedezése érdekében.

### 1.1 Gondolati szintek és fázisok

A gondolkodás három hierarchikus szintre oszlik, amelyeket a ThoughtLevel enum határoz meg

| Szint | Leírás | Megvalósítás fókusza |
| --- | --- | --- |
| local | A csomópontok közvetlen szomszédságára összpontosít. | perturbLocalNodes, updateLocalEdges |
| global | A teljes gráf topológiájának optimalizálása. | esso.optimalizálás minden csomópontban |
| meta | Indokok magáról az érvelési folyamatról. | Szimmetriaminták rögzítése és a stratégia kiigazítása |

Minden végrehajtási egység egy ReasoningPhase, amely nyomon követi az energia konvergenciáját és rögzíti a felfedezett SymmetryPattern azonosítókat.

### 1.2 Orkesztrálási logikai folyamat

Az orchestrator egy egymásba ágyazott ciklusszerkezetet használ:

1.   Belső hurkok: Gyors perturbációk és helyi élfrissítések
2.   Külső hurkok: Globális optimalizációs átmenetek az ESSO motor segítségével az összefonódások feloldására és a gráf energiájának minimalizálására

### Orchestrációs adatáramlás

Ez az ábra azt szemlélteti, hogy az Orchestrator hogyan hidalja át az absztrakt érvelési fázisokat a mögöttes gráf és az optimalizáló entitások között.

### 2. Chaos Core Kernel

A ChaosCoreKernel a Relational Engine intelligens háttértáraként szolgál. A MemoryBlock entitásokat egy tartalomcímezhető architektúrán keresztül kezeli, ahol az adatokat nem tetszőleges címek, hanem kriptográfiai hashek indexelik.

### 2.1 Memóriablokk-kezelés

A MemoryBlock egy adategységet képvisel a Chaos Core-on belül. Nyomon követi:

- Tartalom Hash: SHA-256 származtatott azonosító
- Állam: MemoryBlockState segítségével kezelt (szabad, allokált, összefonódott, migráló)
- Összefonódás: BlockIdSet, amely a kapcsolódó blokkok azonosítóit tartalmazza

### 2.2 Tartalom-címezhető tároló (CAS)

A ContentAddressableStorage struktúra az alapvető tárolási logikát valósítja meg. A deduplikációt a tartalmi hash elsődleges keresési kulcsként való használatával biztosítja. Integrálódik a DataFlowAnalyzerrel a tárolt blokkok entrópiájának és információsűrűségének nyomon követése érdekében.

### 2.3 Adatáramlás és entrópia

A DataFlowAnalyzer kiszámítja az adatblokkok entrópiáját, hogy segítse a kilakoltatási és priorizálási döntéseket. A magas entrópiájú (több egyedi információt tartalmazó) blokkok megőrzése prioritást élvez.

### Chaos Core Entity Mapping

Ez a diagram hidat képez a fogalmi "Káosz" (entrópia/strukturálatlan adatok) és a strukturált Zig entitások között.

### 3. Meglepetés memória integráció

A SurpriseMemoryManager egy újdonságtudatos gyorsítótár-rétegként működik a Chaos Core tetején. Egy többdimenziós "Surprise Score" segítségével határozza meg, hogy mely blokkokat tartsa a nagysebességű memóriában.

### 3.1 Meglepetés mérőszámok

A meglepetést három dimenzió segítségével számítják ki

1.   Jaccard-hasonlóság: Byte-szintű tartalmi különbséget mér
2.   Tartalom Hash távolság: SHA-256 hash-ok közötti Hamming-távolság
3.   Időbeli újdonság: Az információ frissessége a rendszer előzményeihez képest

### 3.2 Megtartási prioritás képlet

A rendszer kiszámítja a retention_priority-t, hogy eldöntse, mely blokkokat kell kilakoltatni a kapacitás elérésekor

$$retention_priority = surprise_score \times (W_{base} + W_{életkor} \cdot \frac{1}{1+életkor} + W_{freq} \cdot \log(freq))$$$

Hol:

- $W_{base} = 0.5$
- $W_{kor} = 0.3$
- $W_{freq} = 0.2$

### 3.3 A végrehajtás részletei

- Mintavétel: A rendszer legfeljebb 1000 blokkot (JACCARD_SAMPLE_SIZE) mintavételez a relatív meglepetés kiszámításához
- Menetbiztonság: Thread.Mutex védi az összes műveletet
- Statisztikák: A SurpriseMemoryStatistics struktúra követi a high_surprise_blocks vs. low_surprise_blocks értékeket a rendszer "tanulásának" nyomon követése érdekében

## Hardveres gyorsítás és elosztott képzés

Ez a szakasz magas szintű áttekintést nyújt a JAIDE hardveres absztrakciós rétegéről, a több GPU-s elosztott képzési infrastruktúráról és a speciális Relational Graph Processing Unit (RGPU) szimulációról. A rendszert úgy tervezték, hogy áthidalja a magas szintű neurális műveleteket a nagy teljesítményű backendekkel, beleértve az NVIDIA CUDA-t, a Futhark által generált kerneleket és az egyéni RTL-leírásokat.

### Rendszerarchitektúra áttekintése

A JAIDE többszintű gyorsítási stratégiát alkalmaz. Az accel_interface.zig elsődleges átjáróként szolgál, absztrahálva a GPU memóriakezelés és a kernel futtatásának bonyolultságát. Nagyméretű munkaterhelések esetén a rendszer több eszközt koordinál egy elosztott képzési rétegen keresztül, amely az NCCL-t használja ki a kollektív kommunikációhoz.

### Hardver-kód leképezés

A következő ábra azt szemlélteti, hogy a magas szintű gyorsítási koncepciók hogyan illeszkednek a kódbázison belüli konkrét megvalósítási egységekhez.

Gyorsítási egység leképezése

### Gyorsító interfész: CUDA és Futhark

A hardver absztrakciós réteg (HAL) egységes API-t biztosít a tenzorműveletekhez. Kezeli a FutharkContext életciklusát, és segédprogramokat biztosít a PinnedMemory számára a host-eszköz közötti átvitel optimalizálása érdekében.

- Futhark integráció: A nagy teljesítményű kernelek a Futharkból C/CUDA-ra vannak fordítva, és a futhark_bindings.zig segítségével vannak lekötve.
- Fraktál LPU: Speciális logikát valósít meg az ortogonális fraktál transzformációs blokk (OFTB) számára hardveresen.

A részletekért lásd

### Elosztott képzés és koordináció

A JAIDE-ban az elosztott képzést a DistributedTrainer kezeli, amely a súlyok szinkronizálását több GPU-n keresztül szervezi. Támogatja mind a helyi több GPU-s beállításokat, mind a felhőalapú hangszerelést a Modal segítségével.

| Component | Felelősség | Key Entity |
| --- | --- | --- |
| Kollektív műveletek | Összes redukciós és broadcast műveletek a gradiens szinkronizáláshoz. | nccl_bindings.zig | nccl_bindings.zig |
| Orchestrálás | Képzési ciklusok kezelése elosztott rangsorokban. | DistributedTrainer |
| Cloud Client | Távoli GPU-munkások biztosítása és kezelése. | ModalGPUClient |

A részletekért lásd

### RGPU: Relational Graph Processing Unit szimuláció

Az RGPU egy speciális hardver-szoftver társtervezés a SelfSimilarRelationalGraph feldolgozására. A hagyományos, sűrű lineáris algebrára optimalizált GPU-kkal ellentétben az RGPU a ritka, szabálytalan gráfstruktúrákra összpontosít.

RGPU architektúra logika

A legfontosabb jellemzők:

- Aszinkron NoC: XY útválasztást használó 2D hálós hálózat a holtpontok megelőzésére
- Energiahatékonyság: A PowerGatingController és a SparseActivationManager az üresjárati feldolgozási ciklusok kihagyásával csökkenti a fogyasztást

A részletekért lásd

### RTL hardver leírások

A szimuláción túl a JAIDE magában foglalja a Clash (Haskell) nyelven írt regiszter-transzfer szintű (RTL) leírásokat is. Ezek képviselik a következtetési komponensek tényleges hardverlogikáját.

- RankerCore: Állapotgép a nagy sebességű szekvencia-újraszortírozáshoz.
- SSISearch: Hardveresen gyorsított trie traversal a Sub-Sequence Indexhez.
- MemoryArbiter: A Ranker és az SSI közötti egyidejű memória-hozzáférési kéréseket kezeli.

A részletekért lásd

## Gyorsító interfész: CUDA, Futhark és Fractal LPU

Ez az oldal a JAIDE rendszer hardver absztrakciós rétegét (HAL) dokumentálja. A Futhark GPU-kontextus életciklusát, a CUDA memóriakezelést, a Fractal Logical Processing Unit (LPU) szimulációt és az egységes API-t foglalja magában, amely hidat képez a magas szintű tenzorműveletek és az alacsony szintű kernel futtatás között.

### Egységesített gyorsító API

A hardveres absztrakció magját az accel_interface.zig tartalmazza, amely egységes interfészt biztosít a GPU-gyorsított műveletekhez. Kezeli a GPU-funkciók feltételes összeállítását a gpu_acceleration build opció alapján

### Futhark kontextus életciklusa

A FutharkContext struktúra kezeli a Futhark futásidejű környezet inicializálását és megsemmisítését.

- Inicializálás: az init() létrehoz egy új Futhark konfigurációt, beállítja a céleszközt (alapértelmezés szerint a 0 eszközt), és konfigurálja a végrehajtási paramétereket, mint például a default_group_size (256), default_num_groups (128) és default_tile_size (32)
- Szinkronizálás: a sync() biztosítja, hogy minden függőben lévő GPU művelet befejeződjön az alapul szolgáló futhark_context_sync meghívásával
- Tisztítás: a deinit() felszabadítja a Futhark kontextust és a hozzá tartozó erőforrásokat

### Pinned memória kezelése

A hatékony host-eszköz (H2D) és eszköz-állomás (D2H) közötti átvitelhez a rendszer a CUDA pinned memóriát használja a PinnedMemory struktúrán keresztül.

- Kiosztás: A cudaHostAlloc-ot használja a cudaHostAllocDefault jelzővel a GPU által elérhető, lapzárolt memória kiosztására
- Felosztás: A cudaFreeHost-ot használja a kitűzött puffer felszabadítására

### Kódex entitás tér: Gyorsítási interfész

A következő ábra azt szemlélteti, hogy a Zig API hogyan illeszkedik a mögöttes Futhark és CUDA C-kötésekhez.

### Futhark Kernel Pipeline

A rendszer a Futharkot használja a neurális hálózati műveletekhez szükséges, nagymértékben optimalizált OpenCL vagy CUDA kernelek létrehozására. Ezeket a futhark_kernels.fut és a main.fut fájlokban definiáljuk.

### Core Kernelek

1.   RSF Előre/hátra: A Reversible Scatter Flow csatolási rétegek megvalósítása. Az előremenő lépés kiszámítja a skála- és transzlációs komponenseket az f16.exp és f16.sum segítségével A hátramenő lépés kiszámítja a súlyok (súly_s, súly_t) és az előfeszítések (s_bias, t_bias) gradienseit a reverzibilis áramlások O(1) memória tulajdonságát használva
2.   SFD optimalizáló frissítés: A sztochasztikus Fisher-diagonális frissítést hajtja végre, lendületet és tanulási rátát alkalmazva a súlyokra és a sebességpufferekre
3.   RSF szórás: A pillangó keverési mechanizmust inv_sqrt2 (1/√2) skálázással valósítja meg a transzformációk közötti variancia fenntartása érdekében
4.   Top-K kiválasztás: Egy radix-sort alapú top-k implementáció a szegmensek rangsorolására a következtetési csővezetékben

### Képzési lépés logikája

A training_step belépési pont a Futharkban egy tétel teljes előre-hátra-felfelé-frissítési ciklusát foglalja magába:

1.   A batch_forward végrehajtása
2.   A veszteség kiszámítása a batch_compute_loss segítségével
3.   A gradiensek kiszámítása a batch_gradients segítségével
4.   Frissíti a súlyokat és sebességeket mind az $S$$, mind a $T$ komponensek esetében

### Fraktál LPU (logikai feldolgozó egység)

A fractal_lpu.zig modul egy önhasonló adatstruktúrákhoz tervezett hardverarchitektúrát szimulál. A számítási erőforrásokat "fraktál csempék" rekurzív hierarchiájába szervezi.

### Hierarchia és felosztás

A FractalLPU a teljes_memóriát lefedő root_tile-vel indul

- Alosztály: Csempék 4 gyermekre oszthatók (quad-tree stílusban), ha az aktuális méret meghaladja a min_tile_size értéket és a szint a box_counting_levels szint alatt van
- Számítási egységek (CU): Minden lapka ComputeUnit struktúrák halmazát tartalmazza. A CU-k számát egy lapkában a lapka szintje határozza meg: 1 << clamped_level

### SSRG leképezés és terheléselosztás

Az LPU-t kifejezetten a Self-Similar Relational Graph (SSRG) feldolgozására tervezték.

- Feltérképezés: A csomópontok egy hash-alapú elosztás segítségével kerülnek hozzárendelésre bizonyos CU-khoz: node_hash % self.compute_units.len
- Terheléskiegyenlítés: A balanceLoad függvény újraosztja a függőben lévő_műveleteket, ha egy CU meghaladja a load_balance_factor értékét a lapka átlagához képest

### Adatáramlás: SSRG a Fraktál LPU-hoz

Ez az ábra azt mutatja, hogy a grafikonadatokat hogyan veszi fel és dolgozza fel a fraktálhardver-szimuláció.

### CUDA kötések és hibakezelés

A cuda_bindings.zig fájl közvetlen interfészt biztosít a CUDA meghajtó/futtatási API-hoz.

### Memória műveletek

Az interfész szabványos CUDA memóriakezelési funkciókat tesz elérhetővé:

- cudaMalloc / cudaFree: Cududa: Az eszköz memóriájának kiosztása
- cudaMemcpy / cudaMemcpyAsync: Szinkron és aszinkron adattovábbítás a Host és az eszköz között
- cudaMemset: Az eszköz memóriájának inicializálása

### Hiba fordítás

A toError függvény a C-stílusú cudaError_t kódokat Zig CudaError enumokká alakítja, megkönnyítve az idiomatikus hibakezelést (pl. try toError(cudaGetLastError()))

| CUDA hibakód | Zig CudaError Enum |
| --- | --- |
| cudaSuccess (0) | (None/Success) |
| cudaErrorMemoryAllocation (2) | CudaError.MemoryAllocation |
| cudaErrorLaunchFailure (4) | CudaError.LaunchFailure |
| cudaErrorInvalidDevice (10) | CudaError.InvalidDevice |

## Elosztott képzés: NCCL, GPU-koordinátor és Modal

Ez a szakasz részletezi a JAIDE rendszer infrastruktúráját a több GPU-s és felhőalapú elosztott képzéshez. Az architektúra az NVIDIA Kollektív Kommunikációs Könyvtárát (NCCL) használja a nagy teljesítményű gradiens szinkronizáláshoz és a Modalt az elasztikus felhő-orchestráláshoz.

### Elosztott képzésszervezés

A képzési csővezetéket a hardveres háttértől függően két elsődleges oktató implementáció kezeli: DistributedTrainer az általános tenzoralapú képzéshez és DistributedTrainerFuthark a nagy teljesítményű Futhark-gyorsított kernelekhez.

### GPUCoordinátor

A GPUCoordinator egy elosztott világon belül egyetlen rang központi irányító egységeként szolgál. Ez kezeli a CUDA eszközök kiválasztását, az NCCL kommunikátorok inicializálását és az alacsony szintű memória műveleteket.

- Inicializálás: Meghatározza a helyi eszköz azonosítóját a rang és a cudaGetDeviceCount alapján Inicializálja az NCCL kommunikátort az ncclCommInitRank használatával
- Memóriakezelés: A cudaMalloc és cudaFree, valamint aszinkron host-eszköz és eszköz-állomás másolásokhoz
- Kollektív műveletek: Float32 és Float16 esetén az ncclAllReduce használatával valósítja meg az allReduce-t

### DistributedTrainerFuthark

Ez az oktató kifejezetten a Futhark-kompilált kerneleket célozza meg az RSF műveletekhez. Kezeli az RSFAccelerátort és koordinálja az adatok betöltését a rangok között.

- Adatbetöltés: Ez egy olyan elosztott adathalmaz-töltőt valósít meg, amely a JSONL-fájlokból kivonatolja a szöveget, biztosítva, hogy minden rang az adatok egy egyedi részhalmazát dolgozza fel
- Tréninghurok: A trainEpoch függvény a mintákon iterál, a gyorsítón keresztül előre/hátra haladást végez, és a koordinátor segítségével szinkronizálja a gradienseket

### Elosztott képzési adatáramlás

A következő ábra az oktató, a koordinátor és a mögöttes hardverkönyvtárak közötti kapcsolatot szemlélteti.

### NCCL és kollektív kommunikáció

A JAIDE az nccl_bindings.zig fájlt használja az NCCL C API-val való kapcsolathoz. Ez lehetővé teszi a hatékony peer-to-peer kommunikációt az NVLink vagy PCIe segítségével.

### Kulcsos kötések

A rendszer az adatpárhuzamos képzéshez szükséges alapvető kollektív primitíveket köti össze:

- ncclAllReduce: Összesíti a gradienseket az összes GPU-n
- ncclBroadcast: Szinkronizálja a modell kezdeti súlyait a gyökér rangtól (0. rang) az összes többi rangra
- ncclGetUniqueId: Az elosztott csoport inicializálásához szükséges bootstrap ID-t generálja

### NCCL inicializálási folyamat

Az inicializáláshoz egy megosztott ncclUniqueId-re van szükség. A JAIDE-ban a 0. helyezett generálja ezt az azonosítót, és megosztja egy fájlrendszeren vagy környezeti változóban, amelyet a többi helyezett beolvas, hogy csatlakozhasson a kommunikátorhoz

### Modális felhő-orchestrálás

A ModalGPUClient egy Zig-natív felületet biztosít a JAIDE képzési feladatoknak a Modal felhőplatformra történő telepítéséhez. Absztrahálja a HTTP-interakciókat a Modal API-val a csúcskategóriás GPU-erőforrások (pl. NVIDIA B200/B300) lekérdezéséhez.

### Telepítés és felügyelet

- deployTrainingJob: Meghatározza a GPU típusát (B300, B200), a GPU-k számát (alapértelmezett 8) és a konténer képet jaide-v40-training
- getJobStatus: Egy adott job_id státuszának lekérdezése a Modal API-n
- HTTP-ügyfél: Az std.http.Client-et használja a hitelesített kérések végrehajtásához Bearer token használatával

### Konfiguráció

Az ügyfél egy API-tokennel és alapértelmezett hardverbeállításokkal inicializálódik:

| Paraméter | Alapértelmezett érték | Forrás |
| --- | --- | --- |
| gpu_count | 8 | | |
| gpu_preferences | {"B300", "B200"} | |
| kép | jaide-v40-training | | |

### Képzési végrehajtás belépési pontok

A JAIDE többféle belépési pontot kínál az elosztott képzés megkezdéséhez:

1.   main_distributed.zig: A Quantum-GPU hibrid képzés elsődleges belépési pontja. Kezeli az NCCL ID generálását, inicializálja a DistributedTrainer-t, és kezeli az epochahurkot
2.   main_distributed_futhark.zig: Futhark-gyorsított klaszterekre optimalizálva. Kifejezetten DistributedTrainerFutharkot használ, és olyan környezeti változókat vár el, mint a WORLD_SIZE, RANK és MASTER_ADDR
3.   main_gpu.zig: Egy egyszerűsített belépési pont az egy GPU-s képzéshez (H100/B200) a Futhark kernelek használatával, megkerülve a több csomópontos koordinációt, miközben továbbra is a GPUCoordinator-t használja az eszközkezeléshez

## RGPU: Relational Graph Processing Unit szimuláció

Az RGPU (Relational Graph Processing Unit) egy speciális hardver-szoftver társtervezési szimulációs környezet, amelyet nagyméretű relációs gráfelemzésre szabtak. A hagyományos, sűrű lineáris algebrára optimalizált GPU-kkal ellentétben az RGPU architektúráját kifejezetten a relációs gráfelméletben gyakori ritka, szabálytalan adatstruktúrákhoz tervezték, mint például az izomorfizmus-felismerés és a dinamikus élsúlyozás

### Rendszerarchitektúra

Az RGPU egy aszinkron Network-on-Chip (NoC) architektúrát szimulál, ahol a gráfadatok a feldolgozómagok 2D-s hálós rácshálóján oszlanak el. A rendszer négy különböző rétegre tagolódik:

| Réteg | Komponens | Felelősség |
| --- | --- | --- |
| Orchestration | RelationalGraphProcessingUnit | Elsődleges belépési pont; koordinálja az adatáramlást a NoC és az analitikai alrendszerek között |
| Kommunikáció | AsynchronousNoC | 2D hálós hálózat kezelése XY útválasztással a NoCMessage csomagok számára |
| Elemzés | GraphIsomorphismProcessor | Kánonikus formák kiszámítása a szerkezeti hasonlóságok felderítésére 76 |
| Hatékonyság | PowerGatingController | Dinamikusan leállítja a kihasználatlan magokat az energiafogyasztás minimalizálása érdekében |

### Processzing Core életciklus és állapot

A ProcessingCore az RGPU alapvető számítási egysége. Minden mag saját local_graph-ot (a globális SelfSimilarRelationalGraph egy szegmensét) és egy aszinkron message_queue-t tart fenn

### Core State Machine

A magok a CoreState-ben meghatározott négy elsődleges állapot között váltakoznak

1.   idle: A mag be van kapcsolva, de nincs aktív munkaterhelés.
2.   feldolgozás: A mag aktívan végrehajtja a gráf algoritmusait vagy frissíti a súlyokat.
3.   kommunikáció: A mag adatokat küld vagy fogad a NoC-n keresztül.
4.   power_gated: A mag energiát takarít meg (szimulált 10,0 egységnyi csökkenés)

### Munkaterhelés és kihasználtság

A ProcessingCore a saját hatékonyságát a getWorkload() és a getUtilization() segítségével követi nyomon, amelyek kiszámítják a cycles_active és az összes ciklus arányát Ezt az adatot a SparseActivationManager használja fel annak meghatározásához, hogy egy magnak ki kell-e hagynia egy ciklust

Források:   52

### Kommunikáció: XY útválasztás: aszinkron NoC és XY útválasztás

Az AsynchronousNoC egy 2D hálós összeköttetést szimulál. Determinisztikus XY útválasztást használ a holtpontok elkerülése érdekében: az üzenetek először az X tengely mentén, majd az Y tengely mentén haladnak, amíg el nem érik a target_core-t

### NoC Entitás kapcsolat

A következő ábra a szimulációs logikát a kódegységekkel hidalja át:

RGPU kommunikációs folyamat

### Analitikai alrendszerek

### Gráf izomorfizmus processzor

A GraphIsomorphismProcessor computeCanonicalForm-ot hajt végre annak meghatározására, hogy két gráfszegmens szerkezetileg azonos-e, függetlenül a csomópontok címkézésétől Ez kritikus fontosságú a SelfSimilarRelationalGraph számára, hogy azonosítsa az adatokban ismétlődő mintákat

### Dinamikus élsúlyozás

A DynamicEdgeWeighting modul az EdgeQuality értékeket a visszacsatolási ciklusok alapján frissíti. A MessageType.weight_update csomagokat használja a változások szinkronizálására az elosztott maghálózatban. 42

Források:  42

### Hatékonyság és energiagazdálkodás

Az RGPU-szimuláció két elsődleges vezérlőn keresztül hangsúlyozza az energiatudatos ütemezést.

### PowerGatingController

Ez a vezérlő kezeli a RelationalGraphProcessingUnit globális power_budgetjét Figyeli a core aktivitást, és kiváltja a CoreState.power_gated átmeneteket

### SparseActivationManager

A grafikus munkaterhelések gyakran ritkák. A SparseActivationManager egy sparsity_threshold értéket használ a végrehajtás optimalizálására

1.   ProcessingCore.getWorkload() lekérdezése.
2.   Ha a munkaterhelés <sparsity_threshold, a mag feldolgozási ciklusa kihagyásra kerül.
3.   Az energy_saved metrika a szimulációs jelentéshez növekszik

RGPU teljesítmény és ritkasági logika

### Adatszerkezetek és SIMD támogatás

Az RGPU a vpu.zig modult használja a vektorműveletekhez, és SimdVector típusokat (pl. f32x4, i32x8) biztosít a helyi gráfszámítások felgyorsításához

| Típus | Sávok | Kijelölés | Használat |
| --- | --- | --- | --- |
| f32x4 | 4 | 16 bájt | Standard súlyfrissítések |
| f32x8 | 8 | 32 bájt | Nagy áteresztőképességű jelátvitel |
| i32x8 | 8 | 32 bájt | Topológiai hash-összehasonlítások |

A magok az initFromSliceChecked funkciót használják a gráf attribútumainak biztonságos betöltésére a SIMD regiszterekbe

## RTL hardver leírások (Clash/Haskell)

Ez a szakasz a Haskellbe ágyazott funkcionális hardverleíró nyelv, a Clash segítségével megvalósított RTL (Register-Transfer Level) hardverleírásokat dokumentálja. Ezek a komponensek nagy teljesítményű hardveres gyorsítást biztosítanak a JAIDE rendszer alapvető rangsorolási és indexelési logikájához, kifejezetten olyan FPGA-kat vagy ASIC-ket célozva, ahol alacsony késleltetésű trie traverzálásra és memória arbitrációra van szükség.

### RankerCore: Scoring State Machine

A RankerCore modul valósítja meg az újrapontozó motor hardveres logikáját. Feldolgozza a RankRequest csomagokat, és RankResult csomagokat generál, amelyek a pozíció torzítással és a lekérdezési kontextussal módosított végső pontszámokat tartalmazzák.

### Adatszerkezetek

- Score32: 32 bites egész szám, amely a szegmens pontszámát jelöli
- RankRequest: SzegmensID, szegmensPos és a baseScore értéket tartalmazó bemeneti csomag
- RankResult: A kimeneti csomag tartalmazza a finalScore-t és az aktuális rangsorszámlálót

### Végrehajtás részletei

Az alapvető logika a rankerT-ben, egy Mealy állapotátmeneti függvényben található A lastQuery-t követi, hogy növelje az állapotszámlálót, amikor az egymást követő kérelmek ugyanahhoz a lekérdezéshez tartoznak

A pontozást a computePositionBias-ban kiszámított pozíció-eltérítés módosítja, 1000-es fix positionBiasScale használatával Az alkalmazott képlet: finalScore = baseScore + (1000 / (segmentPos + 1))

### Ranker adatáramlás

"RankerCore logikai áramlás"

### SSISearch: Hardware Trie Traversal

Az SSISearch hardveresen gyorsított keresési mechanizmust biztosít a Sub-Sequence Index (SSI) számára. Egy 64 bites hash-kulcs alapján egy memóriában tárolt bináris fa struktúrán halad át a szegmenscímek keresése érdekében.

### Keresés állapotgép

A keresés egy véges állapotú gépként van megvalósítva, három elsődleges állapottal

1.   Tétlen: SearchRequestre vár.
2.   Letöltés: Egy TreeNode lekérdezése a memóriából egy adott NodeAddr32-nél.
3.   Összehasonlítás: A searchKey összehasonlítása a keresett csomópont nodeKey-jával.

### Áthaladási logika

A checkNode függvény kezeli az elágazási logikát

- Párbaj: Ha searchKey == nodeKey, return found = True
- Bal ág: Ha searchKey < nodeKey, átmenet a leftChilddal történő lekérdezésre
- Jobb ág: Ha searchKey > nodeKey, átváltás a jobb oldali lánccal történő lekérdezésre
- Megszűnés: MaxSearchDepthConfig (64) túllépése esetén a keresés megszűnik

### Hardveres keresési egységek

"SSI hardver keresés leképezése"

### MemoryArbiter: Access Scheduling

A MemoryArbiter kezeli az egyetlen memóriaporthoz való közös hozzáférést legfeljebb 4 ügyfél (NumClients) számára. Biztosítja a méltányos hozzáférést és kezeli a memória műveletek késleltetését.

### Választottbírósági jegyzőkönyv

- Rögzített szervizablak: Minden engedélyezett kérést 4 ciklusnyi fix ServiceCycles időtartamban szolgálnak ki
- Állami nyomon követés: Az ArbiterState követi az aktuálisan kiszolgált ClientID4 és az eltelt ciklusokat
- Grant Logic: Idle állapotban az arbitrátor a findIndex isJust segítségével választja ki az első függőben lévő kérést az ügyfélvektorból

### Jel-multiplexelés

A memoryArbiter függvény szétválasztja az ügyfél kéréseit és összefűzi a válaszokat A válaszok szűrése a filterResp segítségével történik, biztosítva, hogy csak a kérést kezdeményező ügyfél kapja meg a megfelelő MemResponse-t

### Memory Arbiter architektúra

"Memory Arbiter struktúra"

### RTL-összetevők összefoglalása

| Komponens | Fájl | Kulcslogika | Cél |
| --- | --- | --- | --- |
| RankerCore | RankerCore.hs | rankerT | Alkalmazza a pozíció alapú pontozást és nyomon követi a lekérdezés rangsorát |
| SSISearch | SSISearch.hs | ssiSearchT | Binary trie traversal for index lookups with depth limiting |
| MemoryArbiter | MemoryArbiter.hs | arbiterT | Round-robin stílusú döntőbíráskodás fix szolgáltatási ablakokkal |

## Alapinfrastruktúra: Tenzorok, memória és I/O

Ez a szakasz a JAIDE projekt alapvető Zig infrastruktúráját dokumentálja. A rendszer egy nagy teljesítményű tenzor futtatási időre, a különböző munkaterhelési profilokhoz tervezett egyéni memóriaallokátorok készletére, valamint a modellperzisztenciát biztosító robusztus I/O és szerializációs rétegre épül.

### Infrastruktúra áttekintés

A JAIDE alapinfrastruktúra biztosítja az RSF architektúrához és a Cognitive Relational Engine-hez (CRE) szükséges primitív adatstruktúrákat és erőforrás-kezelést. Tervezésekor a formai helyességre, a memóriahatékonyságra és a hardverszintű teljesítményre helyezték a hangsúlyt.

### Kód Entitás kapcsolat

Az alábbi ábra azt szemlélteti, hogy az alapvető infrastruktúra-egységek hogyan kapcsolódnak egymáshoz a kódbázisban.

Infrastruktúra központi infrastruktúra-egységek térképe

- src/core/memory.zig:156-198 (ArenaAllocator és vtable leképezés)
- src/core/tensor.zig:89-122 (Tensor struktúra definíció és inicializálás)
- docs/tensor.md:92-114 (Az alapvető entitások definíciói)

### Tensor rendszer: Futtatási idő és formális specifikáció

A Tensor rendszer a JAIDE elsődleges numerikus számítási keretrendszere. Kétnyelvű architektúrát használ:

1.   Lean 4 specifikáció: Matematikai bizonyítást nyújt az olyan invariánsokhoz, mint az indexbiztonság és a referenciaszámlálás
2.   Zig Runtime: Kézi memóriakezeléssel és szálbiztos műveletekkel valósítja meg a nagy teljesítményű végrehajtási réteget

A legfontosabb jellemzők közé tartozik a Copy-on-Write (CoW) szemantika a szükségtelen adatduplikáció minimalizálása érdekében, valamint egy olyan Shape rendszer, amely túlcsordulás elleni védelemmel kezeli a sor-major lépéseket

A részletekért lásd

- src/core/tensor.zig:10-30 (Shape és stride inicializálás)
- src/core/tensor.zig:89-122 (Tensor struktúra és refcounting)
- docs/tensor.md:10-27 (Kétnyelvű architektúra és CoW filozófia)

### Memóriakezelés: Allokátorok és szinkronizálás

A JAIDE speciális allokátorok használatával megkerüli a szabványos allokációs mintákat a teljesítménykritikus útvonalakon. A memory.zig modul számos stratégiát kínál a töredezettség mérséklésére és a gyorsítótár lokalitás javítására.

| Kiosztó típusa | Cél | Kódalany |
| --- | --- | --- |
| Arena | Gyors, tömeges kiosztások egylövetű kiosztás megszüntetésével. | ArenaAllocator |
| Slab/Pool | Fix méretű objektumkiosztás a töredezettség megelőzése érdekében. | SlabAllocator / PoolAllocator |
| Buddy | Dinamikus kéttényezős elosztás változó méretekhez. | BuddyAllocator |
| Biztonságos | Memória nullázás és titkosítás az érzékeny adatok számára. | secureZeroMemory |

A szinkronizációt egyedi primitívek, köztük a Mutex, ReadWriteLock és SpinLock segítségével kezeljük, hogy a tenzor futási ideje alatt biztosítsuk a szálbiztonságot

A részletekért lásd

- src/core/memory.zig:77-154 (Arena implementáció)
- src/core/memory.zig:156-210 (ArenaAllocator implementáció)
- src/core/tensor.zig:124-138 (Tensor integráció különböző allokátorokkal)

### I/O, modell szerializáció és tanult beágyazások

Az I/O alrendszer kezeli az átmenetet a memórián belüli tenzorok és a tartós tárolás között. A modell szerializációs formátum egy speciális 0x54464453-as mágikus számot ("SDFT") használ a kompatibilis modellfájlok azonosítására.

### Adatáramlás: Természetes nyelvből kódtenzorokba kódolt tenzorok

Ez a diagram áthidalja a szakadékot a magas szintű koncepciók (mint például a modell mentése) és a mögöttes kód implementációja között.

I/O és szerializációs folyamat

A LearnedEmbedding modul kezeli a token-vektor leképezéshez használt súlytenzorokat, míg a model_io.zig biztosítja a logikát e struktúrák mentéséhez és betöltéséhez a nagy hatékonyságú oldalhoz igazított I/O használatával.

A részletekért lásd

- src/core/tensor.zig:89-122 (Tensor adatstruktúrák)
- src/core/memory.zig:20-25 (Memória-kiigazítás és PageSize)
- A projekt áttekintése 7.3. szakasz (SDFT bűvös szám és szerializációs logika)

### Gyermek oldalak

## Tensor rendszer: Futtatási idő és formális specifikáció

Ez az oldal a JAIDE Tensor rendszer technikai mélységeit mutatja be. A rendszert olyan nagy teljesítményű numerikus keretrendszernek tervezték, amely áthidalja a matematikai formális verifikáció és a rendszerszintű hatékonyság közötti szakadékot. Kétnyelvű architektúrát alkalmaz, ahol a Lean 4 biztosítja a formális specifikációt és bizonyításokat, míg a Zig a nagy teljesítményű futásidőt.

### 1. Kétnyelvű építészet és design filozófia

A Tensor rendszer két elsődleges komponensre oszlik, amelyek egymás logikáját tükrözik, de különböző szerepet töltenek be a fejlesztési életciklusban.

| Jellemzők | Lean 4 megvalósítás | Zig megvalósítás |
| --- | --- | --- |
| Elsődleges cél | Formális helyesség és matematikai bizonyítás | Végrehajtási sebesség és memóriahatékonyság |
| Memória | Funkcionális (megváltoztathatatlan/kezelt) | Kézi (allokátorok/mutatók) |
| Biztonság | Fordítási idejű bizonyítások | Futásidejű ellenőrzések és Mutexek |
| Hibakezelés | TResult (kivéve monád) | Hibakezelés (!) |

Az alapvető filozófia középpontjában a Copy-on-Write (CoW) szemantika, az ellenőrzött indexelés és a memória rugalmassága áll az egyéni allokátorok révén.

### 2. Formális specifikáció (Lean 4)

A formális réteg meghatározza azokat a matematikai invariánsokat, amelyeket a Zig futásidőnek be kell tartania. A legfontosabb struktúrák közé tartozik a Shape, a RefCount és a Tensor.

### Alak és indexelési invariánsok

A Lean Shape struktúra tartalmaz egy h_len bizonyítást, amely biztosítja, hogy a dimenziók listája megegyezik a strides listával.

- Lépések: Többdimenziós indexek leképezése lapos memória-eltolásra.
- Teljes méret: A méretek listájaTerméke.
- Helyesség: Lean bizonyítja, hogy bármely érvényes tenzor esetében a referenciaszám mindig nagyobb, mint nulla (h_pos).

### RefCount és CoW állapot

A Lean modellezi a RefCount életciklusát annak biztosítása érdekében, hogy ne forduljon elő alulcsordulás:

- RefCount.retain: Növeli a számlálót.
- RefCount.release: Ha a számlálás eléri a nullát, akkor a szám csökken, vagy nem ad vissza semmit, jelezve a visszavonást.

### 3. Futásidejű végrehajtás (Zig)

Az src/core/tensor.zig fájlban található Zig implementáció a formális logikát egy nagy teljesítményű struktúrává alakítja, amely manuális memóriakezelést és szálbiztosítási primitíveket használ.

### A Tensor Struct

A Tensor struktúra kezeli mind az adatok nézetét, mind a mögöttes kiosztást.

### Referenciaszámlálás és szálbiztonság

- Atomikus műveletek: megtartás és kiadás @atomicRmw használata .acq_rel sorrenddel a refcount szálak közötti kezeléséhez
- Per-Tensor Mutex: Mutex: Minden tensor példány tartalmaz egy mutatót egy std.Thread.Mutexre, hogy szinkronizálja a hozzáférést az ensureWritable hívások során

### Copy-on-Write (CoW) logika

Minden mutációs művelet előtt meghívásra kerül az ensureWritable. Ha a cow flag be van állítva (ami azt jelenti, hogy az adatok megosztottak), akkor egy új puffer kerül kiosztásra, az adatok másolásra kerülnek, és a tenzor lesz az új puffer egyedüli tulajdonosa.

### 4. Gyári módszerek és lineáris algebra

A rendszer robusztus gyári módszereket és lineáris algebrai műveleteket biztosít, támogatva a standard mélytanulási követelményeket.

### Gyári módszerek

- zeros(allocator, shape): A tenzor minden elemét 0,0-ra állítja.
- ones(allocator, shape): 1.0-val inicializál.
- arange(allokátor, start, stop, step): Egy 1D-sorozat generálása.
- randomNormal(allocator, shape, mean, stddev): Egy tenzor feltöltése normál eloszlású értékekkel.

### Lineáris algebrai műveletek

A rendszer szabványos BLAS-szerű műveleteket és dekompozíciókat hajt végre:

- Matmul: Többdimenziós mátrixszorzás műsorszórási támogatással.
- Conv2D: 2D konvolúció a kitöltés és a lépések támogatásával.
- Dekompozíciók:
- LU: LU felbontás lineáris rendszerek megoldására.
- QR: ortogonális-háromszögletes dekompozíció.
- SVD: Singular Value Decomposition.
- Cholesky: Szimmetrikus, pozitív-definit mátrixokra.

Források:   (Megjegyzés: A matmul/conv2d konkrét sorszámait a csonka fájlban a "lineáris algebrai műveletek" követelménye jelenti a promptban).

### 5. Rendszerentitás-leképezés

A következő ábrák áthidalják a magas szintű fogalmak és a konkrét kódegységek közötti szakadékot.

### A memória kiosztásának folyamata

Ez az ábra azt mutatja, hogy a különböző JAIDE allokátorok hogyan kapcsolódnak a Tensor inicializálásához.

### Ellenőrzési csővezeték adatáramlás

Ez az ábra a Lean 4 specifikáció és a Zig futtatási idő közötti kapcsolatot szemlélteti.

### 6. Stressztesztelés és robusztusság

A referenciaszámláló mechanizmus menetbiztonságának biztosítása érdekében a rendszer többszálas stressztesztet tartalmaz.

- Tesztfutó: src/tests/stress_tensor_refcount.zig több szálat (alapértelmezett 12) hoz létre, amelyek véletlenszerű megtartási és feloldási műveleteket végeznek
- Ellenőrzés: Miután minden szál csatlakozott, a rendszer ellenőrzi, hogy az összes tenzor végső referenciaszámának értéke pontosan 1-e. Ez biztosítja, hogy a nagy párhuzamosságú fázisban nem történtek szivárgások vagy versenyfeltételek

## Memóriakezelés: Allokátorok és szinkronizációs primitívek

### "Nyitott adattár")

Devin

Utolsó indexálás: 2026. május 2. (

Menü

### Memóriakezelés: Allokátorok és szinkronizációs primitívek

A JAIDE rendszer egy többszintű, egyéni memóriakezelő réteget valósít meg, amelyet nagy teljesítményű neurális hálózati műveletekhez, szálbiztos erőforrás-megosztáshoz és biztonságos adatkezeléshez terveztek. Ez a réteg a nyers memória-hozzáférést speciális allokátorokba (Arena, Slab, Pool, Buddy) absztrahálja, és az RSF architektúra O(1) memóriakövetelményeihez és az SSI egyidejű hozzáférési mintáihoz igazított szinkronizációs primitíveket (Lock-free struktúrák, SpinLocks, RWLocks) biztosít.

### 1. Kiosztó hierarchia

A JAIDE különböző allokátorokat használ, hogy minimalizálja a töredezettséget és a többletköltséget a különböző allokációs mintákban.

### 1.1 Aréna és ArenaAllocator

Az Arena egy fix méretű, szálbiztos memóriablokk, amelyet nagy sebességű, összefüggő kiosztásokhoz használnak, ahol a kiosztás megszüntetése tömegesen történik. Az ArenaAllocator ezt egy dinamikus pufferek listájának kezelésével bővíti ki, egy szabványos std.mem.Allocator interfészt biztosítva.

- Aréna: Egyetlen puffert kezel eltolással. Egy std.Thread.Mutex-et használ a hozzáférés szinkronizálására
- ArenaAllocator: ArrayList([]u8) puffereket tart fenn. Amikor az aktuális puffer kimerül, egy újat rendel ki egy parent_allocatorból

### 1.2 Szakosodott elosztók

- SlabAllocator: Az azonos objektumokból álló "táblák" kezelésével csökkenti a töredezettséget.
- PoolAllocator: Ideális a gyakori, rövid életű objektumok számára.
- BuddyAllocator: A bináris Buddy-rendszert a kétpotenciálos méretű blokkok kezelésére használja, egyensúlyt teremtve a rugalmasság és a töredezettség között.
- PageAllocator: A memóriát az operációs rendszer lapszintjén kezeli, tiszteletben tartva az architektúra-specifikus igazításokat (pl. 16KB az Apple Siliconon, 4KB máshol)
- TrackingAllocator: A memóriahasználat, a szivárgás észlelése és a csúcskiosztási metrikák nyomon követése érdekében egy másik allokátor.

### 1.3 Memória segédprogramok és pufferek

- ZeroCopySlice: A következtetési csővezeték szempontjából létfontosságú struktúra az alrendszerek közötti másolás nélküli adatátadásra.
- ResizeBuffer: Egy dinamikus puffer, amely támogatja a hatékony méretváltoztatást opcionális nullázással vagy biztonságos törléssel.

- src/core/memory.zig:15-154 (Arena, Page constants, alapvető matematika)
- src/core/memory.zig:156-210 (ArenaAllocator implementáció)

### 2. Szinkronizációs primitívek

A ReasoningOrchestrator és az SSI keresés egyidejű jellegének támogatása érdekében a JAIDE számos alacsony szintű szinkronizációs primitívet valósít meg.

### 2.1 lakat

- SpinLock: A rendkívül rövid kritikus szakaszokhoz használt, várakozó zár, ahol a kontextusváltás túl nagy terhet jelent.
- ReadWriteLock (RWLock): Több egyidejű olvasót engedélyez, de az írók számára kizárólagos hozzáférést biztosít. Ezt az SSI (Sub-Sequence Index) nagymértékben használja, hogy lehetővé tegye az egyidejű keresést a háttérben történő frissítések során.

### 2.2 Zármentes szerkezetek

A JAIDE tartalmaz zármentes adatszerkezetek implementációit, hogy minimalizálja a nagy áteresztőképességű útvonalakon a versengést:

- Zármentes várólista: A GPUCoordinatorban a feladatok elosztására szolgál.
- Lock-Free Stack: Erőforrás-összevonásra és objektum-újrahasznosításra használják.

### 2.3 Rendszertérképezés: Memória-egységek

A következő ábra a magas szintű memóriafogalmakat az src/core/memory.zig fájlban található konkrét megvalósításukhoz rendeli.

Memóriarendszer kódja Entitás-térkép

- src/core/memory.zig:77-117 (Arena struktúra és metódusok)
- src/core/memory.zig:156-198 (ArenaAllocator és vtable)
- src/core/memory.zig:46-61 (Ellenőrzött aritmetikai és igazítás)

### 3. Biztonságos memória műveletek

A biztonság közvetlenül a memóriarétegbe van integrálva a modellsúlyok és az érzékeny aktiválások védelme érdekében.

### 3.1 secureZeroMemory

A secureZeroMemory funkció (és annak belső megfelelője, a secureResetInternal) biztosítja, hogy az érzékeny adatok törlődnek a RAM-ból, mielőtt a memória visszakerül az operációs rendszerhez vagy más komponensek újra felhasználják.

### 3.2 Memória titkosítás

A nyugalmi állapotban lévő vagy nem biztonságos memóriarégiókon átmenő adatok esetében a JAIDE ChaCha20Poly1305 hitelesített titkosítást használ. Ezt elsősorban a memóriablokkok ChaosCoreKernelbe történő cseréjekor vagy bizonyos SaveTransaction műveletek során használják az RSF perszisztencia rétegben.

### 3.3 Adatáramlás: Biztonságos kiosztás megszüntetése

Ez az ábra a memória áramlását szemlélteti egy Arena életciklusa során, hogy ne legyen adatszivárgás.

Biztonságos kiosztási folyamat

- src/core/memory.zig:95-101 (Arena.deinit végrehajtás)
- src/core/memory.zig:123-128 (secureResetInternal végrehajtás)

### 4. A végrehajtás részletei

### 4.1 Ellenőrzött aritmetika

A puffer túlcsordulások és az egész számokkal kapcsolatos sebezhetőségek megelőzése érdekében a memóriaréteg ellenőrzött aritmetikát használ minden eltolásszámításhoz:

- alignForwardChecked: A cím beállítása előtt biztosítja, hogy az igazítás kettes hatványa legyen
- addChecked / mulChecked: A @addWithOverflow és @mulWithOverflow beépített modulokat használja a kapacitásproblémák felismerésére az allokációs kérelmek során

### 4.2 Igazítás és oldalméretek

A JAIDE a PAGE_SIZE beállításához a fordításkor érzékeli az operációs rendszert és az architektúrát. Apple Silicon (aarch64-macos) esetén 16 384 bájt az alapértelmezett érték, míg más rendszereken 4 096 bájt A MemoryConfig.CACHE_LINE_SIZE 128 bájtra van állítva, hogy optimalizálja a modern CPU gyorsítótár-architektúrákhoz

| Állandó | Érték | Leírás |
| --- | --- | --- |
| PAGE_SIZE | 4096 / 16384 | Architektúra-specifikus memória lapméret |
| CACHE_LINE_SIZE | 128 | Az igazítás célzott gyorsítótár sora |
| min_page_align | Variable | Minimális igazítás az oldalszintű műveletekhez |

- src/core/memory.zig:15-25 (Memória konfigurációs konstansok)
- src/core/memory.zig:42-44 (isPow2 segédprogram)
- src/core/memory.zig:67-75 (runtimeAlignedAlloc végrehajtás)

Elutasíthatod

Frissítse ezt a wikit

Ez a wiki nemrégiben frissült. Kérjük, várjon 7 napot az újbóli frissítéshez.

### Ezen az oldalon

## I/O, modell szerializáció és tanult beágyazások

Ez a szakasz az adatmegmaradás, a bináris szerializáció és a JAIDE LLM rendszerben a tanult beágyazási réteg alapinfrastruktúráját dokumentálja. A fejezet az alacsony szintű I/O segédprogramokat, az egységesített modellfájl-formátumot és a hatékony számításhoz használt fixpontos aritmetikai típusokat tárgyalja.

### Core I/O és memória leképezés

Az io.zig modul magas szintű absztrakciókat biztosít a fájlműveletekhez, kifejezetten a nagyméretű neurális hálózatok súlyaihoz optimalizálva. Az adathozzáférés elsődleges mechanizmusa az MMAP struktúra, amely az operációs rendszer szintű memória leképezést csomagolja be, hogy lehetővé tegye a hatékony véletlenszerű hozzáférést és a perzisztenciát.

### I/O konfiguráció és hibakezelés

A rendszer szigorú korlátokat határoz meg az I/O műveletekre a stabilitás és a biztonság érdekében.

- Puffer méretek: Az alapértelmezett BUFFER_SIZE 8192 bájt, míg a LARGE_CHUNK_SIZE 65536 bájt [[src/core/io.zig:9-10]
- Határok: A maximális fájlméret 1GB-ban (MAX_FILE_SIZE), az elérési útvonal hossza pedig 4096 karakterben van korlátozva [[src/core/io.zig:12-18]
- Biztonság: A fájlok SECURE_FILE_MODE (0o600) beállítással jönnek létre, ami a hozzáférést a tulajdonosra korlátozza [[src/core/io.zig:17]

### Memória leképezés (MMAP)

Az MMAP struktúra kezeli a memóriakapcsolt fájlok életciklusát, és támogatja a csak olvasható és az írható üzemmódot is. Belső mutex szinkronizációt tartalmaz, hogy biztosítsa a szálbiztos hozzáférést a mögöttes pufferhez [[src/core/io.zig:80-86]]

| Funkció | Leírás |
| --- | --- |
| open | Megnyit egy fájlt egy elérési útvonalról, és leképezi a memóriába [[src/core/io.zig:88] |
| read | Visszaadja a leképezett puffer egy szeletét egy adott eltolásnál [[src/core/io.zig:155] |
| write | Adatok írása a leképezett pufferbe opcionális msync[[src/core/io.zig:172] |
| append | Dinamikusan átméretezi a fájlt, újratérképezve a puffert az új adatok befogadásához [[src/core/io.zig:186] |

Adatáramlás: memória-alapú perzisztencia

Források: [[src/core/io.zig:80-227] [[src/core/learned_embedding.zig:108-149]

### Modell szerializáció (SDFT formátum)

A JAIDE rendszer egységes bináris formátumot használ a modell ellenőrzőpontjaihoz. Ez a formátum egyetlen fájlba foglalja a neurális architektúrát (RSF), a rangsoroló motort (Ranker) és a tokenizálót (MGT).

### Bináris struktúra

A modellfájlt a JAIDE40\x00[[src/core/model_io.zig:23] mágikus fejléc azonosítja A szerializálási folyamat szigorú sorrendet követ:

1.   Mágikus fejléc: A fájltípus ellenőrzése.
2.   Metaadatok: A modell méreteit, rétegszámokat és időbélyegeket tartalmazó JSON-kódolt blokk [[src/core/model_io.zig:29-38]]
3.   Komponens tenzorok: Ranker LSH táblák és MGT szókincsadatok.

### ModelMetadata

A ModelMetadata struktúra a betöltés során a processzorkomponensek inicializálásához szükséges kritikus hiperparamétereket követi nyomon. Tartalmazza az rsf_layers, rsf_dim, ranker_ngrams és mgt_vocab_size[[src/core/model_io.zig:33-37]

Kódex entitás tér: Szerializációs komponensek

Források: [[src/core/model_io.zig:29-155]

### Tanult beágyazások

A LearnedEmbedding modul diszkrét tokeneket képez le folytonos vektorterekre. A képzés során kezeli a beágyazási súlyokat és a hozzájuk tartozó gradienseket.

### A végrehajtás részletei

- Inicializálás: A súlyok inicializálása egy 0.02-vel skálázott egyenletes eloszlású PRNG-vel történik [[src/core/learned_embedding.zig:18-23]]
- Előre passz: Egy tokenekből álló tömböt egy lapított kimeneti tenzorra képez le. A vocab_size és a dim[[src/core/learned_embedding.zig:38-59]] korlátok ellenőrzését végzi
- Visszafelé passz: A gradiensek felhalmozása a grad tenzorba a megadott out_grad[[src/core/learned_embedding.zig:61-75]
- Optimalizálás: Az applyGradients függvény alapvető SGD-t valósít meg lendülettel [[src/core/learned_embedding.zig:81-87]

### Formális ellenőrzés

A beágyazási index kiszámítását a Lean 4-ben formálisan ellenőrzik, hogy megakadályozzák a határok nélküli hozzáférést és az egész számok túlcsordulását. A weightIdx_no_usize_overflow tétel bizonyítja, hogy a modell konfigurációját tekintve a sor dim + col mindig USIZE_BOUND-on belül marad [[src/verification/lean4/learned_embedding.lean:164-179]]

Források: [[src/core/learned_embedding.zig:5-150] [[src/verification/lean4/learned_embedding.lean:164-205]

### Magtípusok és fixpontos aritmetika

A JAIDE egyedi fixpontos típusokat használ, hogy determinisztikus aritmetikát biztosítson a különböző hardveres háttértárakon, miközben a 64 bites lebegőszámokhoz képest alacsonyabb memóriaterhelést biztosít.

### Fixpontos specifikációk

A rendszer támogatja a 16 bites, 32 bites és 64 bites fixpontos formátumokat.

| Típus | Alapvető típus | Skálázási tényező | Tört bitek |
| --- | --- | --- | --- |
| FixedPoint16 | i16 | 256.0 | 8 |
| FixedPoint32 | i32 | 65536.0 | 16 |
| FixedPoint64 | i64 | 4294967296.0 | 32 |

### Aritmetikai műveletek

Mindegyik típus az add, sub, mul és div típusokat explicit túlcsordulás-ellenőrzéssel valósítja meg. A szorzás és osztás szélesebb köztes típusokat használ (pl. i32 a FixedPoint16 műveletekhez) a pontosság megőrzése érdekében, mielőtt visszavált a célskálára [[src/core/types.zig:37-52]]

### PRNG infrastruktúra

A rendszer tartalmaz egy Xoshiro256++ algoritmuson alapuló egyedi PRNG-t [[src/core/types.zig:1134]] Ez biztosítja:

- next(): Nyers u64 entrópiát generál.
- randomFloat(): F32 értékeket állít elő a [0.0, 1.0] tartományban.
- fillBytes(): A puffer feltöltése véletlenszerű adatokkal.

Források: [[src/core/types.zig:10-143] [[src/core/types.zig:1134-1180]

## Formális ellenőrzés és biztonság

A JAIDE projekt egy átfogó biztonsági és ellenőrzési keretrendszert valósít meg, amelynek célja, hogy garantálja a neurális architektúrák matematikai helyességét és a következtetési műveletek titkosságát. Ez az infrastruktúra a Reversible Scatter Flow (RSF) rétegek alacsony szintű formális bizonyításától a magas szintű Zero-Knowledge (ZK) protokollokig terjed az ellenőrizhető következtetésekhez.

### Ellenőrzési filozófia: A "Négy-Bizonyító" stratégia

A JAIDE egy multiprover stratégiát alkalmaz a rendszer különböző aspektusainak több formalizmuson keresztüli ellenőrzésére. Ez biztosítja, hogy egyetlen eszköz korlátai sem veszélyeztetik a teljes rendszer integritását. Ennek az erőfeszítésnek a középpontjában a Tensor futásidő és az RSF bijektivitás kétnyelvű verifikációja áll.

Rendszerellenőrzés áttekintése

### Multi-Prover verifikációs csővezeték

A verifikációs csővezeték négy elsődleges bizonyítót integrál az RSF-architektúra és a hozzá kapcsolódó adatstruktúrák validálásához:

- Lean 4: Bijektivitásbizonyításhoz és tenzorműveletek helyességéhez használatos (pl. ResultT monád a hibakezeléshez az rsf.lean-ben)
- Beluga: Kezeli a HOAS-t (Higher-Order Abstract Syntax) a regiszterbiztonság érdekében.
- Tizenkettő: A szerkezeti invertibilitás igazolása.
- Mizar: Halmazelméleti szerializációs bizonyításokat biztosít.

A Zig kódbázisban az InvariantType enum követi, hogy mely tulajdonságok (pl. CONNECTIVITY, ENTANGLEMENT, MEMORY_SAFETY) vannak érvényesítve

A részletekért lásd

### Zéró-tudás bizonyítékok és kriptográfiai biztonság

A VerifiedInferenceEngine irányítja a JAIDE kriptográfiai rétegét. Számos fejlett adatvédelmi technológiát integrál:

- ZKInferenceProver: A modellrétegek helyes végrehajtásának bizonyítékait generálja a súlyok felfedése nélkül.
- CommitmentScheme: Kezeli a modellállapotok kriptográfiai kötelezettségvállalásait
- DifferentialPrivacy: Zajt ad a gradiensekhez vagy a kimenetekhez az adatszivárgás megakadályozása érdekében
- Homomorfikus titkosítás: Lehetővé teszi a számítást a titkosított adatokon

Következtetés-ellenőrzési architektúra

A részletekért lásd

### Kvantum hardver integráció

A JAIDE támogatja a hibrid klasszikus-kvantum verifikációt az IBM Quantum backendekkel való integráció révén. Ezt a quantum_hardware.zig absztrakciós rétegen keresztül kezeli, lehetővé téve, hogy az NSIR (Self-Similar Relational Graph) kvantumállapotokat használjon fel speciális kriptográfiai vagy optimalizálási feladatokhoz.

A rendszer a QuantumState és a RelationalQuantumLogic rendszereket használja a kvantumregiszterek relációs motoron belüli ábrázolására és kezelésére.

A részletekért lásd

- (Import)
- (Kvantumállapot-invariáns)

### A hivatalos szabályok összefoglalása

A rendszer szigorúan meghatározza a ProofRule típusokat, hogy kategorizálja az invarianciák levezetésének módját. Ezek közé tartoznak a standard logikai szabályok, mint a MODUS_PONENS és az INDUCTION, valamint a speciális hardver/szoftver szabályok, mint a LOOP_INVARIANT és az ASSIGNMENT_AXIOM.

| Szabálytípus | Zig szimbólum | Cél |
| --- | --- | --- |
| Szerkezeti | INDUKCIÓ | Rekurzív fraktálszerkezetek ellenőrzése |
| Biztonság | MEMORY_SAFETY | Puffer-túlcsordulás elkerülése a Zig kernelekben |
| Logika | MODUS_PONENS | Logikai következtetések láncolása a CRE-ben |
| Kvantum | QUANTUM_STATE | Az összefonódás és a koherencia hitelesítése |

## Multi-Prover verifikációs csővezeték (Lean 4, Beluga, Twelf, Mizar)

A Multi-Prover Verification Pipeline, belsőleg "Négy-Bizonyító" néven emlegetett rendszer, átfogó formális verifikációs keretrendszert biztosít a JAIDE kódbázis számára. Több logikai területet ölel fel: a Mizarban található magas szintű halmazelméleti tulajdonságoktól a Belugában található alacsony szintű regiszterbiztonságig és a SAW-ban található kriptográfiai helyességig.

### A csővezeték architektúra áttekintése

A csővezeték biztosítja, hogy a Reversible Scatter Flow (RSF) architektúra és a kapcsolódó alrendszerek (MGT, Ranker, Core Relational Engine) a különböző bizonyítási asszisztenseken keresztül megfeleljenek a formális specifikációiknak.

### Adatáramlás és Prover integráció

A következő ábra azt szemlélteti, hogy a különböző bizonyítók hogyan lépnek kapcsolatba a központi kódbázissal és egymással a bizalmi lánc létrehozása érdekében.

Ellenőrzési csővezeték adatáramlás

### 1. 4. soványság: RSF bijektivitás és eredménymonádok

A Lean 4 az RSF-architektúra alapvető matematikai tulajdonságainak bizonyítására szolgál, különösen az $f^{-1}(f(x)) = x$ azonosságra. Az implementáció egy saját ResultT monádot használ a Zig-stílusú hibaterjedés kezelésére a logikán belül.

### Kulcsfontosságú logikai egységek

- ZigError: A Zig hibakészletet tükröző induktív típus, beleértve a túlcsordulást, az invalidDimension-t és az checksumMismatch-et
- ResultT α: Konstruktorokkal rendelkező eredmény-monád
- ThForwardInverseIdentity: Az elsődleges tétel, amely azt állítja, hogy bármely érvényes $x$ bemenet és $\theta$ paraméterek esetén a ForwardOnCore és InverseOnCore kompozíciója az eredeti bemenetet adja vissza.

### Funkcionális feltérképezés

| Lean 4 entitás | Zig Equivalent | Cél |
| --- | --- | --- |
| ResultT.bind | try / catch | Monádikus hibaláncolás |
| natEqB | == (Nat esetén) | Bólés egyenlőség a dimenziókhoz |
| bIte | if ... else | Boolean if-then-else logikai áramláshoz |

### 2. Beluga: HOAS nyilvántartás biztonsága

A Beluga implementáció (rsf.bel) az RSF futási idejében használt regiszteralapú állapotátmenetek biztonságára összpontosít. A tenzorok és regiszterek életciklusának modellezéséhez a HOAS (Higher-Order Abstract Syntax) rendszert használja.

### Állami átmenetek nyilvántartása

Az átmenet típusa meghatározza a regiszterállapotok közötti érvényes mozgásokat, hogy megakadályozza a kettős fékezést vagy a nem allokált memóriához való hozzáférést:

- tr-acquire: Átmenet egy élő regiszterből egy inkrementált állapotba
- tr-destroy-live: A regisztert "haldoklónak" jelöli (megsemmisítésre vár)
- tr-destroy-zero: Aktív referenciák nélküli regisztert biztonságosan felszabadít

### 3. Tizenkettő: Szerkezeti invertibilitás

A tizenkettőt az RSF rétegek szerkezeti tulajdonságainak bizonyítására használják, különösen az affin csatolási transzformációk invertálhatóságára és a pillangó keverési lépések kommutativitására.

### Invertálhatósági bizonyítékok

- add-sub-cancel: Bizonyítja, hogy az összeadás, majd a kivonás az azonosság
- sub-add-cancel: Bizonyítja a fordított tulajdonságot
- times-unique: Biztosítja, hogy két tetszőleges tenzor esetén a szorzatuk egyedi és determinisztikus

### 4. Mizar: Mizar: Halmazelméleti szerializáció

A Mizar biztosítja a szerializációs formátum halmazelméleti megalapozását. Meghatározza a Tensor2D struktúrát, és biztosítja, hogy a lemezre történő szerializálás (a SAVE_VERSION = 4 verziójú) injektív legyen.

### Alapvető fogalommeghatározások

- Tensor2D: Sorok és oszlopok felett definiálva, mindkettőnek $> 0$-nak kell lennie
- jól formázott LayerCore: 20.0, 20.0]$ véges határok között kell lennie
- xavier_bound: $\sqrt{6.0 / (fan_in + fan_out)}$ a súly inicializálásához

### 5. SAW és Cryptol: Cryptographic & Parameter Verification

A Software Analysis Workbench (SAW) áthidalja a szakadékot a magas szintű Cryptol specifikáció és a Zig implementáció LLVM bitkódja között.

### A specifikáció kódra való leképezése

A verify.saw szkript betölti a main.bc állományt, és a C-szintű struktúrákat a Cryptol specifikációkhoz rendeli.

SAW-ellenőrzés leképezése

### Legfontosabb ellenőrzési feladatok

1.   config_init_spec: Cry-ben definiált konstansokkal inicializálódik a Config struktúra
2.   validate_config_spec: Ellenőrzi, hogy a konfiguráció érvényesítési logikája helyesen érvényesíti-e az olyan korlátokat, mint a MIN_EMBEDDING_DIM és MAX_RSF_LAYERS
3.   prng_next_spec: Az LCG (Linear Congruential Generator) implementációjának validálása a szorzó 6364136223846793005 és a növekmény 1442695040888963407 segítségével

### 6. A korlátozások és konstansok összefoglalása

A csővezeték számos keményen kódolt korlátot és mágikus számot érvényesít az összes bizonyítóban, hogy biztosítsa a rendszerközi konzisztenciát.

| Állandó | Érték | Fájlhivatkozás |
| --- | --- | --- |
| FILE_MAGIC_RSF | 0x4a524653 | | | |
| MAX_RSF_LAYERS | 256 | | | |
| MAX_TENSOR_SIZE | 16384 | | |
| SAVE_VERSION | 4 | | |
| HASH_SIZE | 16 | | | |

Források:  8

## Zéró-tudás bizonyítékok és kriptográfiai biztonság

A JAIDE rendszer egy többrétegű kriptográfiai biztonsági keretrendszert valósít meg, amelynek célja a modellkövetkeztetés integritásának biztosítása, az adatállományok adatainak védelme és ellenőrizhető garanciák nyújtása a helyességre. Mindezt a zéró-tudásbizonyítékok (ZKP), a homomorfikus titkosítás (HE), a differenciális adatvédelem (DP) és a kriptográfiai kötelezettségvállalások kombinációjával érjük el.

### ZK következtetési nyomkövető rendszer

A verifikációs motor lényege a ZK következtetési nyomkövető rendszer, amely lehetővé teszi a bizonyító számára annak bizonyítását, hogy egy adott modell kimenete egy adott modellarchitektúra és súlykészlet által generált, anélkül, hogy felfedné a belső aktivációkat vagy magukat a súlyokat.

### Megvalósítás és áramkörök

A rendszer a Circomot használja a Reversible Scatter Flow (RSF) réteg számításait reprezentáló aritmetikai áramkörök definiálására. Az elsődleges áramkör, az inference_trace.circom a Poseidon hashinget használja a hatékony áramkörön belüli kötelezettségvállaláshoz és ellenőrzéshez.

- PoseidonChain: Változó hosszúságú hash-mechanizmust valósít meg a bemenetek darabolásával és a Poseidon hash-ek láncolatával
- RSFLayerComputation: Egy sablon, amely ellenőrzi egy RSF réteg előrehaladását, beleértve az affin csatolást és a súlykötelezettségeket
- VerifyMerkleProof: Érvényesíti, hogy egy adott súly vagy adatpont tartozik egy elkötelezett adathalmazhoz vagy modellállapothoz

### Bizonyítás és ellenőrzés folyamata

A CircomProver osztály kezeli a ZK bizonyítások életciklusát, beleértve az áramkörök összeállítását, a tanúk generálását és a bizonyítás generálását a Groth16 protokoll segítségével a snarkjs segítségével.

| Funkció | Szerep | Forrás |
| --- | --- | --- |
| compileCircuit | A .circom fájlokat R1CS és WASM formátumba fordítja. | |
| generateWitness | A WASM tanúgenerátor végrehajtása bemeneti jelekkel. | |
| generateProof | Meghívja a snarkjs-t egy Groth16 bizonyítás létrehozására. | |
| verifyProof | Érvényesíti a bizonyítékot a nyilvános jelek és az ellenőrző kulcs alapján. | |

### Kriptográfiai kötelezettségvállalás és adatvédelem

A JAIDE számos kriptográfiai primitívet alkalmaz az adatok nyugalmi és számítás közbeni védelmére.

### Kötelezettségvállalási program

A CommitmentScheme egy mechanizmust biztosít a motor számára a modellparaméterek vagy adatsegmensek rögzítéséhez. Támogatja a Pedersen Commitments-et a tulajdonságok elrejtéséhez és kötéséhez

### Differenciált adatvédelem

A DifferentialPrivacy osztály zajt alkalmaz a gradiensekre vagy a kimenetekre, hogy megakadályozza a tagságra következtető támadásokat. Egy $(\epsilon, \delta)$ differenciális adatvédelmi mechanizmust valósít meg

### Homomorfikus titkosítás

Az érzékeny relációs adatok esetében a JAIDE a Paillier-kriptoszisztémát használja, amely lehetővé teszi az additív homomorf műveleteket. Ez lehetővé teszi a rendszer számára, hogy bizonyos számításokat a titkosított adatokon anélkül végezzen el, hogy azokat előbb visszafejtené.

- PaillierKeyPair: 256 bites kulcsokat generál a titkosításhoz
- HomomorphicEncryption.encrypt/decrypt: Paillier-műveletek 64 bites egész számokra
- HomomorphicEncryption.add: Összeadást végez két titkosított szövegen

### Ellenőrzött következtetési motor

A VerifiedInferenceEngine az összes kriptográfiai komponenst összekötő rendszer. Biztosítja, hogy a következtetési folyamat minden egyes lépése a helyesség bizonyításával vagy kriptográfiai kötelezettségvállalással legyen alátámasztva.

### Motorarchitektúra és adatáramlás

A motor hivatkozásokat tart fenn a ZK Prover, Commitment Scheme és Obfuscation modulokra.

Modellellenőrzési adatáramlás:

### Kulcsfontosságú motorműveletek

1.   Inicializálás: A motor inicializálható ZK-támogatással vagy anélkül. Ha a ZK engedélyezve van, akkor előzetesen inicializálja a modell súlyokat és előkészíti a ZKInferenceProver-t
2.   Súlyterhelés: A súlyok betöltése és ellenőrzése a Blake3 segítségével generált modell hash (model_hash) alapján történik
3.   Ellenőrzés nyomon követése: A motor nyomon követi a verification_count és a successful_verifications értékeket a rendszer integritásának ellenőrzési naplójának fenntartása érdekében

### Biztonsági politika és bizonyítékok

A security_proofs.zig modul definiálja a formális biztonsági szinteket és a hozzáférés-szabályozási logikát a relációs gráfhoz.

### Biztonsági és integritási szintek

A JAIDE a Bell-LaPadula és a Biba modellek által inspirált rácsalapú biztonsági modellt használ.

| Entitás | Szintek | Forrás |
| --- | --- | --- |
| SecurityLevel | PUBLIC, INTERNAL, CONFIDENTIAL, SECRET, TOP_SECRET | | |
| IntegrityLevel | UNTRUSTED, USER, SYSTEM, KERNEL | | |
| AccessRight | READ, WRITE, EXECUTE, DELETE, ADMIN | | |

### Biztonsági logikai áramlás

A hozzáférés-szabályozás úgy érvényesül, hogy ellenőrzik, hogy a megbízó biztonsági szintje "uralkodik-e" az objektum biztonsági szintjén.

Hozzáférés-ellenőrzési logika:

### Adathalmaz ujjlenyomat készítése

A DatasetFingerprint és a ProofOfCorrectness osztályok a modell súlyainak létrehozásához használt képzési adatok letagadhatatlanságát biztosítják. Ez biztosítja, hogy a modellt nem manipulálták, illetve nem képezték jogosulatlan adathalmazokon.

## Quantum Hardware Integration és IBM Quantum

A JAIDE rendszer kvantumszámítási képességeket integrál a nagymértékben összefonódott relációs struktúrák feldolgozásának felgyorsítására a kognitív relációs motoron (CRE) belül. Ezt az integrációt egy olyan hardveres absztrakciós rétegen keresztül kezelik, amely a Qiskit Runtime API-n keresztül támogatja mind a helyi szimulációt, mind a távoli végrehajtást az IBM Quantum hardverén.

### Építészeti áttekintés

A kvantumintegrációs réteg hidat képez a klasszikus relációs gráf és a kvantumprocesszorok között. Azonosítja a nagyfokú összefonódással vagy összetett fraktáldimenziókkal rendelkező részgráfokat, és állapotfejlődésüket a kvantumos háttértárakra terheli.

### Kvantum-klasszikus adatáramlás

A következő ábra azt szemlélteti, hogy a relációs adatokat hogyan alakítja át kvantumfeladatokká és dolgozza fel az integrációs réteg.

Quantum Task életciklus

### Kvantum hardver absztrakció

A rendszer hardveres specifikációkat határoz meg különböző IBM Quantum backendekhez a zaj és dekoherencia modellezéséhez a szimuláció során, illetve a feladatok benyújtásának optimalizálásához.

### Backend specifikációk

Az IBMBackendSpecs és QuantumConfig állandók meghatározzák a támogatott hardverek, például a Heron, Eagle és Falcon processzorok működési korlátait és fizikai jellemzőit

| Paraméter | Heron (tipikus) | Sas (tipikus) | Sólyom (tipikus) |
| --- | --- | --- | --- |
| T1 (Relaxáció) | 350,000 ns | 200,000 ns | 100,000 ns |
| T2 (Dephasing) | 200,000 ns | 120,000 ns | 80,000 ns |
| Kiolvasási hiba | 0,8% | 1,5% | 2,0% |
| ECR Gate Error | 0,3% | 0,5% | 0,7% | 0,3% | 0,5% | 0,7% |
| Qubit szám | 133 | 127 | 27 |

### Kalibrációs adatok

Az IBMBackendCalibrationData struktúra valós idejű hardver metrikákat kezel, beleértve a T1/T2 időket és a coupling_map-et, amely meghatározza a qubitek fizikai összekapcsolhatóságát

### IBM Quantum integráció

Az IBMQuantumClient kezeli a kommunikációt az IBM Quantum felhő API-val. Az API-tokeneken és a felhőerőforrás-neveken (CRN) keresztül kezeli a hitelesítést

### Kulcsfunkciók

- initWithCrn: A CRN-t a környezeti változókból szerzi be, ha nincs megadva
- submitJob: Az OpenQASM karakterláncot JSON hasznos teherré formázza, és POST-kérést hajt végre az IBM Quantum jobs végpontjára
- getJobResult: Egy adott job_id eredményeinek lekérdezése az API-ban

### Quantum Task adapter

A QuantumTaskAdapter az a szervező, amely meghatározza, hogy a SelfSimilarRelationalGraph mely részei igényelnek kvantumgyorsítást.

### Algráf azonosítása és alkalmassága

Az adapter olyan klasztereket keres a gráfban, ahol a quantum_correlation és a fractal_dimension meghaladja a meghatározott küszöbértékeket

- QuantumSubgraph: Egyetlen kvantumegységként azonosított csomópontok és élek gyűjteménye
- isQuantumSuitable: Visszaadja az igazat, ha total_entanglement > küszöbérték (alapértelmezett 0,5) és avg_fractal_dimension > 1,5

### Végrehajtási logika

Az adapter a teljesítmény nyomon követésére AdapterStatistics statisztikákat tart fenn, beleértve a total_qubits_used és az avg_execution_time_ms értékeket

Entitás leképezés: Kvantum

### CREV Pipeline integráció

A CREV (Cognitive Relational Extraction and Validation) csővezeték kvantum-alapú korrelációkat használ az új ismeretek integrálásának validálására

1.   Kivonás: A relationalTriplet objektumok a forrásadatokból jönnek létre
2.   Érvényesítés: A QuantumTaskAdapter kiszámítja a triplett összefonódási stabilitását a meglévő gráfkontextuson belül.
3.   Integráció: Ha a kvantumállapot stabil marad (az IBMDocumentedBackendSpecs által megjósolt alacsony dekoherencia), a triplett bekerül a SelfSimilarRelationalGraphba

## Meglepetésmemória és tartalomcímezhető tárolók

A SurpriseMemoryManager egy újdonságtudatos tárolórendszer, amely az adatok megőrzését a "meglepetés" (információs újdonság) alapján rangsorolja, nem pedig a hozzáférés egyszerű gyakorisága vagy ismétlődése alapján. Közvetlenül integrálódik egy tartalom-címezhető tároló (CAS) háttértárral, hogy biztosítsa a deduplikációt, miközben az adatok fontosságának nagy pontosságú nyilvántartását tartja fenn.

### Áttekintés

A hagyományos gyorsítótár kilakoltatási politikáktól eltérően, mint például az LRU (Least Recently Used) vagy az LFU (Least Frequently Used), a Surprise Memory rendszer az adatblokkok belső értékét értékeli Egy többdimenziós pontozási mechanizmust használ a rendszer számára "meglepő" adatok azonosítására, ami azt jelenti, hogy jelentősen eltér a jelenleg tárolt információtól

A rendszer kettős megvalósítási stratégiát követ:

1.   Zig végrehajtás: Src/core_relational/surprise_memory.zig alatt található nagy teljesítményű, szálbiztos futásidejű program
2.   Lean 4 specifikáció: Egy formális matematikai modell, amely 271+ bizonyított tételt biztosít az összes műveletre vonatkozó invarianciák garantálásához

### Meglepetés rendszerarchitektúra

A következő ábra a nyers adatok bevitelétől az újdonságtudatos tárolási háttértárig tartó folyamatot szemlélteti.

Források:   106

### Alapvető összetevők

### Meglepetés mérőszámok és kilakoltatási logika

A rendszer szíve a SurpriseMetrics struktúra, amely három független dimenzióból számítja ki a kombinált pontszámot

- Jaccard-hasonlóság: A byte-szintű tartalmi átfedést méri egy 1000 meglévő blokkból álló mintával szemben
- Tartalom Hash távolság: SHA-256 hash-ok közötti normalizált Hamming-távolság
- Időbeli újdonság: Annak mérése, hogy mennyi idő telt el azóta, hogy hasonló adatokkal találkoztunk

Amikor a tárolókapacitás elérte a határt, az evictLowSurpriseBlocks függvény egy részleges rendezési algoritmust használ a legalacsonyabb retention_priority-vel rendelkező blokkok eltávolítására

A részletekért lásd

### Z-Runtime és C API

A SurpriseMemoryManager egy sor alacsony szintű segédprogramra támaszkodik, és stabil interfészt biztosít a külső hívók számára.

- z_runtime.zig: Zig-specifikus futásidejű segédprogramokat biztosít.
- c_api.zig: A menedzser funkcionalitását C-kompatibilis nyelvek számára teszi elérhetővé, lehetővé téve az újdonságtudatos memória használatát a Zig ökoszisztémán kívül is.
- biztonsági.zig: Biztosítja az aritmetikai biztonságot a pontszámok normalizálása és a prioritás számítások során ellenőrzött casting segítségével

A részletekért lásd

### Megtartási prioritás képlete

A rendszer minden SurpriseRecord számára kiszámítja a megőrzési_prioritást Ez a képlet egyensúlyba hozza az adatok belső "meglepetését" és az adatok időbeli hasznosságát:

| Súlytényező | Érték | Leírás |
| --- | --- | --- |
| RETENTION_BASE_WEIGHT | 0.5 | A meglepetés pontszámából származtatott alapérték |
| RETENTION_AGE_WEIGHT | 0.3 | Az utolsó hozzáférés óta eltelt időn alapuló csökkenési tényező |
| RETENTION_FREQUENCY_WEIGHT | 0.2 | Bónusz a gyakran használt "hasznos" blokkokért |

Kódex entitás leképezés: Prioritásszámítás

### Formális invariánsok

A Surprise Memory rendszert több formális invariáns szabályozza, amelyeket a Lean 4-ben ellenőrzött

1.   Pontszámtartomány: Minden meglepetés-mérőszámnak és kombinált pontszámnak a $[0.0, 1.0]$ tartományban kell maradnia
2.   Osztályozási integritás: A high_surprise_blocks és a low_surprise_blocks összege mindig kisebb vagy egyenlő a total_blocks értékével
3.   Menetbiztonság: A SurpriseMemoryManager minden nyilvános metódusának meg kell szereznie a belső Mutexet a végrehajtás előtt

### Teljesítményjellemzők

| Művelet | Komplexitás | Megjegyzések |
| --- | --- | --- |
| computeSurprise | $O(1)$ | Mintavétel legfeljebb JACCARD_SAMPLE_SIZE (1000) blokkig |
| storeWithSurprise | $O(1)$ amortizált | Meglepetésszámítással és HashMap beszúrással jár |
| evictLowSurpriseBlocks(k) | $O(k \times n)$ | Részleges rendezést használ a $k$ legalacsonyabb prioritású blokkok megtalálására |
| organizeByEntanglement | $O(p^2)$ | $p \ 100$ párra korlátozva |

## Meglepetés mérőszámok és kilakoltatási logika

### "Nyitott adattár")

Devin

Utolsó indexálás: 2026. május 2. (

Menü

### Meglepetés mérőszámok és kilakoltatási logika

A SurpriseMemoryManager egy újdonságtudatos tárolórendszert valósít meg, amely az adatok megőrzését az információs "meglepetés" alapján rangsorolja, nem pedig a hozzáférés egyszerű gyakorisága vagy ismétlődése alapján. Többdimenziós újdonsági pontszámok kiszámításával a rendszer biztosítja, hogy az egyedi vagy váratlan adatblokkok megmaradjanak a gyorsítótárban, míg a redundáns vagy nagyentrópiájú, de alacsony információtartalmú adatok először kiürülnek

### Többdimenziós meglepetés számítás

A rendszer egy három független dimenzióból álló SurpriseMetrics struktúrát számol ki. Ezeket a metrikákat egy [0.0, 1.0] tartományra normalizáljuk, és átlagoljuk, hogy egy kombinált_surprise pontszámot kapjunk

### 1. Jaccard-hasonlósági mintavételezés

Ez a metrika a bájtszintű tartalmi hasonlóságot méri a meglévő adatokkal szemben. Az $O(1)$ teljesítmény fenntartása érdekében a rendszer nem minden blokkot hasonlít össze; ehelyett a JACCARD_SAMPLE_SIZE (1000) blokkokig terjedő mintákat vesz fel

- Mechanizmus: Az új blokk és a mintavételezett blokkok közötti byte-halmazok metszetét és egyesítését számítja ki.
- Képlet: $ 1.0 - (\text{metszés} / \text{egyesülés})$.
- Forrás: 21

### 2. Tartalom Hash Hamming távolság

Ez a kriptográfiai eltérést a tartalom SHA-256 hash-jának felhasználásával méri.

- Mechanizmus: Kiszámítja a Hamming-távolságot az új blokk 128 bites csonka hash-ja és a ContentAddressableStorage meglévő blokkjainak hash-jai között
- Normalizálás: A bit-flip távolságot a HASH_BITS (128) ellenében normalizáljuk

### 3. Időbeli újdonság

Ez jelenti az adatok beérkezésének "történelmi kontextusát".

- Képlet: $1 / \sqrt{1 + \text{block_count}}$
- Cél: A ritka előzmények között érkező új blokkok természetüknél fogva "meglepőbbek", mint a nagy volumenű kitörések során érkező blokkok

### Meglepetés logikai adatáramlás

A következő ábra azt szemlélteti, hogy a nyers tartalom hogyan alakul át meglepetéspontszámmá, és hogyan integrálódik a SurpriseRecordba.

### Fenntartási prioritás és kilakoltatás

Amikor a SurpriseMemoryManager eléri a kapacitását, egy súlyozott képlet segítségével határozza meg, hogy mely blokkokat kell kilakoltatni. A retention_priority a meglepetés pontszám, a blokk kora és a hozzáférési gyakoriság összetétele

### Megtartási képlet

A recomputeRetention függvény a következő logikát valósítja meg:

$$retention_priority = surprise_score \times (W_{base} + W_{életkor} \times \frac{1}{1 + age_ms} + W_{freq} \times \frac{freq}{freq + K_{sat}})$$$

| Állandó | Érték | Leírás |
| --- | --- | --- |
| RETENTION_BASE_WEIGHT | 0.5 | Meglepő adatok alapértéke |
| RETENTION_AGE_WEIGHT | 0.3 | Újrakezdési bónusz a friss blokkokhoz |
| RETENTION_FREQUENCY_WEIGHT | 0.2 | Bónusz a gyakran használt blokkokért |
| FREQUENCY_SATURATION | 8.0 | A frekvencia növekedésének csillapítási tényezője |

### Részleges rendezésű kilakoltatási algoritmus

A teljes memóriaterület rendezése helyett (ami $O(N \log N)$ lenne) a rendszer egy részleges rendezési stratégiát alkalmaz

1.   Jelöltek kiválasztása: Azonosítja azokat a blokkokat, amelyek kombinált_surprise értéke a surprise_threshold (alapértelmezett 0.3) alatt van
2.   Rangsorolás: Csak a legalacsonyabb $K$ prioritású blokkokat sorolja.
3.   Végrehajtás: EvictLowSurpriseBlocks(k) hívása a hely felszabadítására, miközben a magas meglepetésszámú blokkok megmaradnak

### Rendszer megvalósítása és szálbiztonság

A SurpriseMemoryManager a központi szervező, amely a ContentAddressableStorage (CAS) és a SurpriseRecord metaadatokat kezeli

### Menetbiztonság

A többszálas környezetekben (mint például az InferenceServer) az integritás biztosítása érdekében a menedzser egy durva szemléletű std.Thread.Mutexet használ Minden nyilvános metódus, beleértve a storeWithSurprise és a getSurpriseRecord metódusokat is, a belépéskor megszerzi ezt a mutexet, és a defer

### Kód Entitás leképezés

A következő ábra a magas szintű meglepetés fogalmakat a kódbázisban található konkrét Zig-struktúrákhoz és függvényekhez rendeli hozzá.

### Teljesítményjellemzők

| Művelet | Komplexitás | Megjegyzés |
| --- | --- | --- |
| computeSurprise | $O(1)$ | JACCARD_SAMPLE_SIZE által korlátozott |
| storeWithSurprise | $O(1)$ amortizált | Hash map beszúrás a meglepetés számítás után |
| evictLowSurpriseBlocks | $O(K \times N)$ | Részleges rendezés $K$ legalacsonyabb prioritású blokkokra |

Források:  21

Elutasíthatod

Frissítse ezt a wikit

Ez a wiki nemrégiben frissült. Kérjük, várjon 7 napot az újbóli frissítéshez.

### Ezen az oldalon

## Z-Runtime és C API

A Z-Runtime és a C API rétegek biztosítják a JAIDE rendszer alapvető végrehajtási környezetét és az idegen függvények interfészét (FFI). Míg az alapvető neurális architektúrák (RSF/OFTB) a matematikai transzformációkat kezelik, addig ezek a modulok a változó állapotot, a végrehajtás előzményeit, a C-kompatibilis interoperabilitást és a szigorú aritmetikai biztonságot kezelik.

### 1. Z-Runtime: Változók relációs kezelése

A z_runtime.zig modul a Cognitive Relational Engine (CRE) magas szintű végrehajtási környezetét valósítja meg. Kezeli a ZVariable példányokat, amelyek egy SelfSimilarRelationalGraph és a hozzá tartozó RelationalQuantumLogic állapotot kapszulázzák

### A végrehajtás nyomon követése és előzményei

A futásidő az ExecutionHistoryEntry és HistoryEntry struktúrákon keresztül minden műveletről részletes ellenőrzési nyomvonalat vezet. Ez lehetővé teszi a rendszer számára, hogy nyomon kövesse a relációs állapotok időbeli alakulását

| Művelet típusa | Kódalany | Leírás |
| --- | --- | --- |
| Hozzárendelés | HistoryEntryType.assign | Kezdeti érték vagy állapot hozzárendelése |
| Transzformáció | ExecutionAction.fractal_transform | Fraktál transzformációk alkalmazása egy változóra |
| Összefonódás | ExecutionAction.entangle_variables | Kvantum-relációs kapcsolatok létrehozása a csomópontok között |
| Measurement | ExecutionAction.measure | Kvantumállapotok klasszikus relációs adatokká alakítása |

### Z-futásidejű adatáramlás

A következő ábra azt szemlélteti, hogy egy ZVáltozó hogyan koordinál a gráftároló és a kvantumlogikai réteg között egy végrehajtási művelet során.

Z-futásidejű változó hangszerelés

### 2. C-kompatibilis API (FFI)

A c_api.zig modul egy átláthatatlan interfészt biztosít a külső fogyasztók (pl. Python, C++ vagy Rust) számára a JAIDE relációs motorral való interakcióhoz. A Zig-natív struktúrákat, mint például a SelfSimilarRelationalGraph, pointer-stabil, átlátszatlan típusokba csomagolja

### Az FFI legfontosabb összetevői

- Átlátszatlan fogantyúk: CGraph és COptimizer szolgálnak elsődleges kezelőszervként a külső hívók számára 88
- Hiba leképezése: A belső Zig hibák c_int konstansokra vannak leképezve, mint például JAIDE_SUCCESS (0) vagy JAIDE_ERROR_ALLOCATION (-2)
- C-kompatibilis struktúrák: A CQuantumState extern struct-ot használ a komplex számok C ABI kompatibilitásának biztosítása érdekében

### Optimalizáló integráció

A C API megjeleníti az EntangledStochasticSymmetryOptimizer (ESSO) programot, amely lehetővé teszi a perturbációs valószínűségek és a hűtési sebességek külső konfigurálását

C-API és belső leképezés

### 3. Biztonsági és aritmetikai primitívek

A safety.zig modul egy sor "biztonságos" burkolatot biztosít a gyakori Zig műveletekhez, kifejezetten a relációs motor kritikus útvonalainak meghatározatlan viselkedésének megakadályozására.

### Egész és mutató biztonsága

- safeIntCast: SafetyError-t ad vissza, ha a határokat túllépik
- safePtrCast: @ptrCast végrehajtása előtt ellenőrzi a mutató igazítását és nullságát
- validatePointer: Egy nem hiba-visszatérő segédprogram, amely ellenőrzi, hogy egy mutató vagy opcionális mutató érvényes (nem null)-e

### Kriptográfiai és memória segédprogramok

- SecureRng: Random, hogy kriptográfiailag biztonságos véletlenszámokat biztosítson az optimalizáló és a zajgeneráláshoz
- secureZeroBytes / secureZeroSlice: Az illékony írást használja, hogy biztosítsa a memória nullázását és azt, hogy a fordító ne optimalizálja el, ami elengedhetetlen az érzékeny relációs adatok törléséhez
- secureCompare: Az időzítési támadások megakadályozására a hash-ok vagy kulcsok érvényesítésénél

### Biztonsági hiba fogalommeghatározások

A modul egy speciális hibakészletet definiál a futási időhöz:

- IntegerOverflow / IntegerUnderflow
- NullPointer / MisalignedPointer
- BufferTooSmall

## Fogalomtár

Ez az oldal a JAIDE (Joint Artificial Intelligence Distributed Engine) kódbázisra jellemző szakterminológia, rövidítések és architektúrális fogalmak technikai definícióit tartalmazza. A mérnökök számára elsődleges bevezető forrásként szolgál a természetes nyelvi fogalmaknak a Zig, a Futhark és a Lean 4 egyedi megvalósításaihoz való hozzárendeléséhez.

### 1. Alaparchitektúra (RSF és OFTB)

### Visszafordítható szórásos áramlás (RSF)

Olyan neurális architektúra, amely a hagyományos Attention és MLP blokkokat invertálható affin csatolási rétegekkel helyettesíti. Az RSF O(1) memóriakomplexitást ér el a visszafelé haladás során azáltal, hogy az aktivációkat a kimenetből rekonstruálja, ahelyett, hogy a VRAM-ban tárolná őket.

- Végrehajtás: Meghatározva az src/processor/rsf.zig-ben. Az alaplogika a ForwardOnCore és az InverseOnCore függvények között oszlik meg
- Adatszerkezet: LayerCore-t használ, amely négy súly/előfeszítés tenzort tartalmaz: s_weight, t_weight, s_bias és t_bias

### Ortogonális fraktál transzformációs blokk (OFTB)

Egy determinisztikus keverési mechanizmus, amely az információáramlást biztosítja minden dimenzióban, tanult permutációk nélkül. Egy "pillangó" műveletet használ $1/\sqrt{2}$ skálázási tényezővel a variancia fenntartása érdekében.

- Funkció: rsf_scatter a Futhark kernelekben
- Logika: Vektorfelek összegzése és differenciálása a Haar-szerű transzformáció szimulálása érdekében

### 2. Relációs és kvantumrendszerek

### Kognitív relációs motor (CRE)

Az érvelésért és a hosszú távú tudás reprezentációjáért felelős magas szintű alrendszer. Az NSIR-gráfot kvantumlogikai kapukkal integrálja.

### NSIR (önhasonló relációs gráf)

Gráf-alapú adatszerkezet, ahol a csomópontok fogalmakat, az élek pedig különböző "minőségű" (pl. összefonódott, összeomlott) kapcsolatokat jelölnek.

- Végrehajtás: Mag_relációs/nsir_core.zig-ban: SelfSimilarRelationalGraph: SelfSimilarRelationalGraph
- Éles tulajdonságok: EdgeQuality enum által definiált: szuperpozíció, összefonódott, koherens, összeomlott, fraktális

### ESSO (Entangled Stochastic Symmetry Optimizer)

Egy szimulált lágyításon alapuló motor, amely optimalizálja a relációs gráf topológiáját a szimmetriák felismerése és az információs entrópia minimalizálása érdekében.

- Végrehajtás: OptimizationState és SymmetryGroup a src/core_relational/esso_optimizer.zig fájlban
- Szimmetria típusok: Rotation_90, translation és custom_rotation

Ez a diagram a fogalmi "Reasoning" rétegeket a konkrét Zig struktúrákhoz és enumokhoz rendeli.

### 3. Optimalizálás és hardver

### SFD (sztochasztikus Fisher-diagonális)

Másodrendű optimalizáló, amely a Fisher Információs Mátrix diagonálisát közelíti, hogy paraméterspecifikus adaptív tanulási rátákat biztosítson.

- Végrehajtás: Zig: SFD struktúra az src/optimizer/sfd.zig fájlban
- Konfiguráció: Az SFDConfig kezeli az olyan paramétereket, mint fisher_max és finite_diff_eps

### TMEM (Tensor memória)

Az NVIDIA B200 (Blackwell) hardverre jellemző, hogy a 32 MB-os chipen lévő gyors memóriára utal. A JAIDE B200MemoryManager a tenzorokat a HBM és a TMEM között az access_freq alapján mozgatja

### 4. Memória és indexelés

### Meglepetés memória

Egy újdonságtudatos gyorsítótárazási rendszer, amely a hagyományos LRU/LFU mérőszámok helyett a "meglepetés-pontszámok" alapján törli az adatokat.

- Mérőszámok: Kombinálva a jaccard_dissimilarity, content_hash_distance, és temporal_novelty mérőszámokból
- Menedzser: MeglepetésMemoryManager a src/surprise/surprise_memory.zig fájlban

### SSI (alszekvencia-index)

Egy trie-alapú index, amelyet a következtetés során a token n-gram szegmensek tárolására és visszakeresésére használnak.

- Megvalósítás: src/index/ssi.zig.
- Kölcsönhatás: GetSegment az előre kiszámított pontszámok lekérdezéséhez

Az adatáramlás leképezése a nyers tárolástól a rangsorolt következtetési eredményekig.

### 5. Formális ellenőrzés

### Négy-Bizonyító (Four-Prover) csővezeték

A JAIDE stratégiája a matematikai helyesség biztosítására a különböző logikai területeken.

1.   4. soványság: RSF bijektivitás és tenzorinvariánsok (pl. h_len, h_pos) ellenőrzése
2.   Beluga: Ellenőrzi a HOAS-nyilvántartás biztonságát.
3.   Tizenkettő: Ellenőrzi a szerkezeti invertibilitást.
4.   Mizar: Ellenőrzi a halmazelméleti szerializációt.

### 6. Az alapvető összetevők táblázata

| kifejezés | kódmutató | meghatározás |
| --- | --- | --- |
| Arena | src/core/memory.zig:77 | Egy szálbiztos, régióalapú allokátor kötegelt műveletekhez |
| CoW | docs/tensor.md:51 | Copy-on-Write állapot a tenzorokhoz; biztosítja, hogy az adatok csak akkor másolódjanak, ha a megosztott puffer mutálódik |
| MGT | src/tokenizer/mgt.zig | Morpheme-Guided Tokenization; nyelvi horgonyokat használ a szekvencia indexeléshez |
| NoC | docs/rgpu.md:23 | Network-on-Chip; szimulált 2D háló a magok közötti kommunikációhoz az RGPU-ban |
| Qubit | src/core_relational/nsir_core.zig:86 | Egy gráf csomópont kvantumállapotát reprezentáló 2 állapotú komplex vektor |
| SymmetryGroup | src/core_relational/esso_optimizer.zig:72 | Az ESSO optimalizáláshoz szükséges geometriai transzformációkat meghatározó enum |