use bignat::nat_to_limbs;
use bignat::BigNat;
use num_bigint::BigUint;
use poly::Polynomial;
use rand::thread_rng;
use sapling_crypto::bellman::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Parameters, Proof};
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::{pairing::Engine, Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use std::fs;
use std::path::Path;
use std::str::FromStr;
use OptionExt;

const DATA_PATH: &str = "./data";
const PARAMETER_FILE_PATH: &str = "./data/vdf_zkp_parameter.data";

const ROUND_KEYS: &[&str] = &[
  "0",
  "20888961410941983456478427210666206549300505294776164667214940546594746570981",
  "15265126113435022738560151911929040668591755459209400716467504685752745317193",
  "8334177627492981984476504167502758309043212251641796197711684499645635709656",
  "1374324219480165500871639364801692115397519265181803854177629327624133579404",
  "11442588683664344394633565859260176446561886575962616332903193988751292992472",
  "2558901189096558760448896669327086721003508630712968559048179091037845349145",
  "11189978595292752354820141775598510151189959177917284797737745690127318076389",
  "3262966573163560839685415914157855077211340576201936620532175028036746741754",
  "17029914891543225301403832095880481731551830725367286980611178737703889171730",
  "4614037031668406927330683909387957156531244689520944789503628527855167665518",
  "19647356996769918391113967168615123299113119185942498194367262335168397100658",
  "5040699236106090655289931820723926657076483236860546282406111821875672148900",
  "2632385916954580941368956176626336146806721642583847728103570779270161510514",
  "17691411851977575435597871505860208507285462834710151833948561098560743654671",
  "11482807709115676646560379017491661435505951727793345550942389701970904563183",
  "8360838254132998143349158726141014535383109403565779450210746881879715734773",
  "12663821244032248511491386323242575231591777785787269938928497649288048289525",
  "3067001377342968891237590775929219083706800062321980129409398033259904188058",
  "8536471869378957766675292398190944925664113548202769136103887479787957959589",
  "19825444354178182240559170937204690272111734703605805530888940813160705385792",
  "16703465144013840124940690347975638755097486902749048533167980887413919317592",
  "13061236261277650370863439564453267964462486225679643020432589226741411380501",
  "10864774797625152707517901967943775867717907803542223029967000416969007792571",
  "10035653564014594269791753415727486340557376923045841607746250017541686319774",
  "3446968588058668564420958894889124905706353937375068998436129414772610003289",
  "4653317306466493184743870159523234588955994456998076243468148492375236846006",
  "8486711143589723036499933521576871883500223198263343024003617825616410932026",
  "250710584458582618659378487568129931785810765264752039738223488321597070280",
  "2104159799604932521291371026105311735948154964200596636974609406977292675173",
  "16313562605837709339799839901240652934758303521543693857533755376563489378839",
  "6032365105133504724925793806318578936233045029919447519826248813478479197288",
  "14025118133847866722315446277964222215118620050302054655768867040006542798474",
  "7400123822125662712777833064081316757896757785777291653271747396958201309118",
  "1744432620323851751204287974553233986555641872755053103823939564833813704825",
  "8316378125659383262515151597439205374263247719876250938893842106722210729522",
  "6739722627047123650704294650168547689199576889424317598327664349670094847386",
  "21211457866117465531949733809706514799713333930924902519246949506964470524162",
  "13718112532745211817410303291774369209520657938741992779396229864894885156527",
  "5264534817993325015357427094323255342713527811596856940387954546330728068658",
  "18884137497114307927425084003812022333609937761793387700010402412840002189451",
  "5148596049900083984813839872929010525572543381981952060869301611018636120248",
  "19799686398774806587970184652860783461860993790013219899147141137827718662674",
  "19240878651604412704364448729659032944342952609050243268894572835672205984837",
  "10546185249390392695582524554167530669949955276893453512788278945742408153192",
  "5507959600969845538113649209272736011390582494851145043668969080335346810411",
  "18177751737739153338153217698774510185696788019377850245260475034576050820091",
  "19603444733183990109492724100282114612026332366576932662794133334264283907557",
  "10548274686824425401349248282213580046351514091431715597441736281987273193140",
  "1823201861560942974198127384034483127920205835821334101215923769688644479957",
  "11867589662193422187545516240823411225342068709600734253659804646934346124945",
  "18718569356736340558616379408444812528964066420519677106145092918482774343613",
  "10530777752259630125564678480897857853807637120039176813174150229243735996839",
  "20486583726592018813337145844457018474256372770211860618687961310422228379031",
  "12690713110714036569415168795200156516217175005650145422920562694422306200486",
  "17386427286863519095301372413760745749282643730629659997153085139065756667205",
  "2216432659854733047132347621569505613620980842043977268828076165669557467682",
  "6309765381643925252238633914530877025934201680691496500372265330505506717193",
  "20806323192073945401862788605803131761175139076694468214027227878952047793390",
  "4037040458505567977365391535756875199663510397600316887746139396052445718861",
  "19948974083684238245321361840704327952464170097132407924861169241740046562673",
  "845322671528508199439318170916419179535949348988022948153107378280175750024",
  "16222384601744433420585982239113457177459602187868460608565289920306145389382",
  "10232118865851112229330353999139005145127746617219324244541194256766741433339",
  "6699067738555349409504843460654299019000594109597429103342076743347235369120",
  "6220784880752427143725783746407285094967584864656399181815603544365010379208",
  "6129250029437675212264306655559561251995722990149771051304736001195288083309",
  "10773245783118750721454994239248013870822765715268323522295722350908043393604",
  "4490242021765793917495398271905043433053432245571325177153467194570741607167",
  "19596995117319480189066041930051006586888908165330319666010398892494684778526",
  "837850695495734270707668553360118467905109360511302468085569220634750561083",
  "11803922811376367215191737026157445294481406304781326649717082177394185903907",
  "10201298324909697255105265958780781450978049256931478989759448189112393506592",
  "13564695482314888817576351063608519127702411536552857463682060761575100923924",
  "9262808208636973454201420823766139682381973240743541030659775288508921362724",
  "173271062536305557219323722062711383294158572562695717740068656098441040230",
  "18120430890549410286417591505529104700901943324772175772035648111937818237369",
  "20484495168135072493552514219686101965206843697794133766912991150184337935627",
  "19155651295705203459475805213866664350848604323501251939850063308319753686505",
  "11971299749478202793661982361798418342615500543489781306376058267926437157297",
  "18285310723116790056148596536349375622245669010373674803854111592441823052978",
  "7069216248902547653615508023941692395371990416048967468982099270925308100727",
  "6465151453746412132599596984628739550147379072443683076388208843341824127379",
  "16143532858389170960690347742477978826830511669766530042104134302796355145785",
  "19362583304414853660976404410208489566967618125972377176980367224623492419647",
  "1702213613534733786921602839210290505213503664731919006932367875629005980493",
  "10781825404476535814285389902565833897646945212027592373510689209734812292327",
  "4212716923652881254737947578600828255798948993302968210248673545442808456151",
  "7594017890037021425366623750593200398174488805473151513558919864633711506220",
  "18979889247746272055963929241596362599320706910852082477600815822482192194401",
  "13602139229813231349386885113156901793661719180900395818909719758150455500533",
];

pub fn permutation_out_side<F: PrimeField>(input: F) -> F {
  let mut x = input;
  for i in 0..91 {
    x.add_assign(&F::from_str(ROUND_KEYS[i]).unwrap());

    let mut x2 = x;
    x2.square();

    let mut x4 = x2;
    x4.square();

    let mut x7 = x4;
    x7.mul_assign(&x2);
    x7.mul_assign(&x);

    x = x7;
  }
  x
}

macro_rules! init_big_uint_from_str {
  ($var:ident, $val:expr) => {
    let $var = BigUint::from_str($val).unwrap();
  };
}

#[derive(Debug)]
pub struct Input<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub _temp: Option<E>,

  pub two_two_t: BigUint,
  pub p_minus_one: BigUint,
  pub q_minus_one: BigUint,

  pub quotient: BigUint,
  pub remainder: BigUint,

  pub g: BigUint,
  pub y: BigUint,

  pub commitment: E::Fr,
}

impl<E> Input<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub fn new(two_two_t: BigUint, p_minus_one: BigUint, q_minus_one: BigUint, quotient: BigUint, remainder: BigUint, g: BigUint, y: BigUint) -> Self {
    let commitment = permutation_out_side(E::Fr::from_str(y.to_string().as_str()).unwrap());
    Input {
      commitment,
      _temp: None,
      two_two_t,
      p_minus_one,
      q_minus_one,
      quotient,
      remainder,
      g,
      y,
    }
  }
}

#[derive(Clone)]
pub struct Param {
  pub word_size: usize,
  pub two_two_t_word_count: usize,

  pub quotient_word_count: usize,
  pub prime_word_count: usize,
  pub n_word_count: usize,
}
pub struct VdfCircuit<E>
where
  E: Engine,
{
  pub inputs: Option<Input<E>>,
  pub params: Param,
}

impl<E> Circuit<E> for VdfCircuit<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    let two_two_t = BigNat::alloc_from_nat(cs.namespace(|| "2^{2^t}"), || Ok(self.inputs.as_ref().grab()?.two_two_t.clone()), self.params.word_size, self.params.two_two_t_word_count)?;
    let p_minus_one = BigNat::alloc_from_nat(cs.namespace(|| "p-1"), || Ok(self.inputs.as_ref().grab()?.p_minus_one.clone()), self.params.word_size, self.params.prime_word_count)?;
    let q_minus_one = BigNat::alloc_from_nat(cs.namespace(|| "q-1"), || Ok(self.inputs.as_ref().grab()?.q_minus_one.clone()), self.params.word_size, self.params.prime_word_count)?;

    let quotient = BigNat::alloc_from_nat(cs.namespace(|| "quotient"), || Ok(self.inputs.as_ref().grab()?.quotient.clone()), self.params.word_size, self.params.quotient_word_count)?;
    let remainder = BigNat::alloc_from_nat(cs.namespace(|| "remainder"), || Ok(self.inputs.as_ref().grab()?.remainder.clone()), self.params.word_size, self.params.n_word_count)?;

    let g = BigNat::alloc_from_nat(cs.namespace(|| "g"), || Ok(self.inputs.as_ref().grab()?.g.clone()), self.params.word_size, self.params.n_word_count)?;
    let y = BigNat::alloc_from_nat(cs.namespace(|| "y"), || Ok(self.inputs.as_ref().grab()?.y.clone()), self.params.word_size, self.params.n_word_count)?;

    let one = BigNat::alloc_from_nat(cs.namespace(|| "1"), || Ok(BigUint::from(1usize)), 1, 1)?;

    let one_poly = Polynomial::from(one.clone());
    let p_minus_one_poly = Polynomial::from(p_minus_one.clone());
    let q_minus_one_poly = Polynomial::from(q_minus_one.clone());
    let quotient_poly = Polynomial::from(quotient.clone());
    let remainder_poly = Polynomial::from(remainder.clone());
    let pi_n_poly = p_minus_one_poly.alloc_product(cs.namespace(|| "(p-1)(q-1) = pi_n(totient)"), &q_minus_one_poly)?;

    let p_poly = Polynomial::from(p_minus_one_poly).sum(&one_poly);
    let q_poly = Polynomial::from(q_minus_one_poly).sum(&one_poly);
    let n_poly = p_poly.alloc_product(cs.namespace(|| "pq = n"), &q_poly)?;

    let qpi_n = quotient_poly.alloc_product(cs.namespace(|| "quotient * pi_n(totient)"), &pi_n_poly)?;
    let qpi_n_plus_remainder = Polynomial::from(qpi_n).sum(&remainder_poly);

    let max_word = BigUint::from(std::cmp::min(p_minus_one.limbs.len(), q_minus_one.limbs.len())) * &p_minus_one.params.max_word * &q_minus_one.params.max_word;
    let pi_n = BigNat::from_poly(Polynomial::from(pi_n_poly), self.params.word_size, max_word.clone()); // 1: pi&q_minus_one.params.max_word-1n
    let n = BigNat::from_poly(Polynomial::from(n_poly), self.params.word_size, max_word.clone()); // 1: n

    let max_word = BigUint::from(std::cmp::min(quotient.limbs.len(), pi_n.limbs.len())) * &quotient.params.max_word * &pi_n.params.max_word + &remainder.params.max_word;
    let qpi_n_plus_remainder_big_nat = BigNat::from_poly(Polynomial::from(qpi_n_plus_remainder), self.params.word_size, max_word);

    let gr_n = g.pow_mod(cs.namespace(|| "g^r mod n"), &remainder, &n)?;

    two_two_t.inputize(cs.namespace(|| "two_two_t"))?;
    g.inputize(cs.namespace(|| "g"))?;
    n.inputize(cs.namespace(|| "n"))?;

    let expected_output: E::Fr = E::Fr::from_str(gr_n.value.clone().unwrap_or(num_bigint::BigUint::default()).to_string().as_str()).unwrap_or(E::Fr::zero());
    let allocated_expected_output = AllocatedNum::alloc(cs.namespace(|| "Allocate y"), || Ok(expected_output))?;
    let calculated_commitment = permutation(cs.namespace(|| "MIMC(g^r mod n) / MIMC(y)"), allocated_expected_output)?;

    let allocated_commitment = AllocatedNum::alloc(cs.namespace(|| "Allocate commitment"), || Ok(self.inputs.grab()?.commitment))?;
    let is_same_commitment = AllocatedNum::equals(cs.namespace(|| "Check commitment and MIMC(g^r mod n) / MIMC(y)"), &allocated_commitment, &calculated_commitment)?;

    two_two_t.is_equal(cs.namespace(|| "2^{2^t} == q * pi_n + r"), &qpi_n_plus_remainder_big_nat)?;
    y.equal(cs.namespace(|| "y == g^r mod n"), &gr_n)?;
    Boolean::enforce_equal(cs.namespace(|| "commitment == MIMC(g^r mod n) MIMC(y)"), &is_same_commitment, &Boolean::Constant(true))?;
    Ok(())
  }
}

pub struct VdfZKP<E>
where
  E: Engine,
{
  vdf_param: Param,
  pub params: Option<Parameters<E>>,
}

impl<E> VdfZKP<E>
where
  E: Engine,
{
  pub fn new() -> VdfZKP<E> {
    VdfZKP {
      params: None,
      vdf_param: Param {
        word_size: 64,
        two_two_t_word_count: 4,
        quotient_word_count: 2,
        n_word_count: 2,
        prime_word_count: 1,
      },
    }
  }

  pub fn setup_parameter(&mut self) {
    let rng = &mut thread_rng();

    self.params = {
      let circuit = VdfCircuit::<E> { inputs: None, params: self.vdf_param.clone() };
      Some(generate_random_parameters(circuit, rng).unwrap())
    };
  }

  pub fn export_parameter(&self) {
    if fs::create_dir_all(DATA_PATH).is_ok() == false {
      return;
    };
    let file = std::fs::File::create(PARAMETER_FILE_PATH).expect("File creatation is failed");
    self.params.as_ref().unwrap().write(file).unwrap();
  }

  pub fn import_parameter(&mut self) {
    if Path::new(PARAMETER_FILE_PATH).exists() == false {
      self.setup_parameter();
      self.export_parameter();
      return;
    }

    let file = std::fs::File::open(PARAMETER_FILE_PATH).expect("File not found");
    self.params = Some(Parameters::read(file, true).unwrap());
  }

  pub fn generate_proof(&self, _two_two_t: &str, _p_minus_one: &str, _q_minus_one: &str, _quotient: &str, _remainder: &str, _g: &str, _y: &str) -> Proof<E> {
    init_big_uint_from_str!(two_two_t, _two_two_t);
    init_big_uint_from_str!(p_minus_one, _p_minus_one);
    init_big_uint_from_str!(q_minus_one, _q_minus_one);
    init_big_uint_from_str!(quotient, _quotient);
    init_big_uint_from_str!(remainder, _remainder);
    init_big_uint_from_str!(g, _g);
    init_big_uint_from_str!(y, _y);

    let rng = &mut thread_rng();

    let circuit = VdfCircuit::<E> {
      inputs: Some(Input::new(two_two_t, p_minus_one, q_minus_one, quotient, remainder, g, y)),
      params: self.vdf_param.clone(),
    };

    create_random_proof(circuit, self.params.as_ref().unwrap(), rng).unwrap()
  }

  pub fn verify(&self, proof: Proof<E>, _two_two_t: &str, _g: &str, _n: &str) -> bool {
    init_big_uint_from_str!(two_two_t, _two_two_t);
    init_big_uint_from_str!(g, _g);
    init_big_uint_from_str!(n, _n);

    let pvk = prepare_verifying_key(&self.params.as_ref().unwrap().vk);

    let mut inputs: Vec<<E as ScalarEngine>::Fr> = nat_to_limbs::<<E as ScalarEngine>::Fr>(&two_two_t, self.vdf_param.word_size, self.vdf_param.two_two_t_word_count);
    inputs.extend(nat_to_limbs::<<E as ScalarEngine>::Fr>(&g, self.vdf_param.word_size, self.vdf_param.n_word_count));
    inputs.extend(nat_to_limbs::<<E as ScalarEngine>::Fr>(&n, self.vdf_param.word_size, self.vdf_param.n_word_count));

    verify_proof(&pvk, &proof, &inputs).unwrap()
  }
}

pub fn permutation<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, input: AllocatedNum<E>) -> Result<AllocatedNum<E>, SynthesisError> {
  let mut x = input;
  for i in 0..91 {
    let mut cs = cs.namespace(|| format!("round {}", i));
    let rk_val = E::Fr::from_str(ROUND_KEYS[i]).unwrap();
    let x2 = AllocatedNum::alloc(cs.namespace(|| "x2 result"), || {
      let mut t = x.get_value().grab()?.clone();
      t.add_assign(&rk_val);
      t.square();
      Ok(t)
    })?;
    cs.enforce(|| "x2 = (x+c)^2", |lc| lc + x.get_variable() + (rk_val, CS::one()), |lc| lc + x.get_variable() + (rk_val, CS::one()), |lc| lc + x2.get_variable());
    let x4 = x2.square(cs.namespace(|| "x4"))?;
    let x6 = x4.mul(cs.namespace(|| "x6"), &x2)?;
    let x7 = AllocatedNum::alloc(cs.namespace(|| "x7"), || {
      let mut xc = x.get_value().grab()?.clone();
      xc.add_assign(&rk_val);
      let mut t = x6.get_value().grab()?.clone();
      t.mul_assign(&xc);
      Ok(t)
    })?;
    cs.enforce(|| "x7 = (x+c)x6", |lc| lc + x.get_variable() + (rk_val, CS::one()), |lc| lc + x6.get_variable(), |lc| lc + x7.get_variable());
    x = x7;
  }
  Ok(x)
}

#[cfg(test)]
mod tests {
  use super::*;
  use sapling_crypto::bellman::pairing::bn256::Bn256;
  use std::time::Instant;

  const G: &str = "2";
  const TWO_TWO_T: &str = "2";

  const P_MINUS_ONE: &str = "2";
  const Q_MINUS_ONE: &str = "4";

  const QUOTIENT: &str = "0";
  const REMAINDER: &str = "2";
  const Y: &str = "4";
  const N: &str = "15";

  #[test]
  fn gadget_test_with_setup_parameter() {
    let mut vdf_zkp = VdfZKP::<Bn256>::new();
    let start = Instant::now();
    vdf_zkp.setup_parameter();
    let duration = start.elapsed();
    println!("Setup {:?}", duration);

    vdf_zkp.export_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(TWO_TWO_T, P_MINUS_ONE, Q_MINUS_ONE, QUOTIENT, REMAINDER, G, Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, TWO_TWO_T, G, N);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }

  #[test]
  fn gadget_test_with_load_parameter() {
    let mut vdf_zkp = VdfZKP::<Bn256>::new();
    vdf_zkp.import_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(TWO_TWO_T, P_MINUS_ONE, Q_MINUS_ONE, QUOTIENT, REMAINDER, G, Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, TWO_TWO_T, G, N);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }
}
