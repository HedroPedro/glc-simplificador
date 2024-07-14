use {regex::Regex, std::{collections::{HashMap, HashSet}, env, fs, ops::Not, panic, vec}};

const VOID_VAL : &str = "&";

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2{
        panic!("Falta de argumentos"); 
    }
    let prod_rules = get_build_rules(&args[1]);
    let simplified_rules = simplify_rules(&prod_rules);
}

fn get_build_rules(file_path : &str) -> HashMap<char, Vec<String>> {
    let mut rules = HashMap::new();
    let string = fs::read_to_string(file_path).expect("ok");
    let split: Vec<&str> = string.split("\n").collect();
    for string in split{
        let vector: Vec<&str> = string.split("->").collect();
        let key = vector[0].trim().chars().next().expect("Key");
        rules.insert(key, vector[1].split("|").map(|x| x.trim().to_string()).collect());
    }
    return rules;
}

fn simplify_rules(build_rules : &HashMap<char, Vec<String>>) -> HashMap<char, Vec<String>> {   
    let simplified_rule = cut_useless_prods(build_rules);
    convert_rules_to_chomsky(&simplified_rule);
    return simplified_rule;
}

fn remove_void(build_rules : &HashMap<char, Vec<String>>) -> HashMap<char, Vec<String>> {
    let mut new_build_rules: HashMap<char, Vec<String>> = HashMap::new();
    let mut null_set = HashSet::<char>::new();
    let mut null_prev_size : usize;  
    for (k, vect) in build_rules{
        for val in vect {
            match (*val).cmp(&VOID_VAL.to_string()){
                std::cmp::Ordering::Greater => {},
                std::cmp::Ordering::Less => {},
                std::cmp::Ordering::Equal => {
                    null_set.insert(*k);
                    break;
                }
            }
        }
    }

    null_prev_size = null_set.len();
    loop {
        for (k, vect) in build_rules{
            vect.iter().for_each(|x| {
                if !null_set.contains(k){
                    null_set.insert(*k);
                    for char in x.chars(){
                        if !null_set.contains(&char){
                            null_set.remove(k);
                            break;
                        }
                    }
                }
            });
        }
        if null_set.len() == null_prev_size{
            break;
        }
        null_prev_size = null_set.len();
    }

    for (key, vect) in build_rules {
        let mut new_vect : Vec<String> = vect.into_iter().filter(| x | **x != "&").map(|x| (*x).to_string()).collect();
        
        if *key == 'S' && vect.into_iter().any(|x| x == &"&") {
            new_vect.push("&".to_string());
        } 
        
        for i in 0..new_vect.len() {
            for null_key in &null_set {
                if new_vect[i].contains(*null_key){
                    let mut new_string = String::new();
                    let strings : Vec<String> = new_vect[i].split(*null_key).map(|x| x.to_string()).collect();
                    new_string.push_str(&strings[0]);
                    new_string.push_str(&strings[1]);
                    if new_string.len() == 0 {
                        continue;
                    }
                    new_vect.push(new_string.trim().to_string());  
                }
            }
        }
        new_build_rules.insert(*key, new_vect);
    }

    return  new_build_rules;
}

fn remove_sub_prod(build_rules : &HashMap<char, Vec<String>>) -> HashMap<char, Vec<String>> {
    let mut new_prod_rules = remove_void(build_rules);
    let re = Regex::new(r"^[A-Z]{1}$").unwrap();
    let mut fechos: HashMap<char, Vec<String>> = new_prod_rules.to_owned().into_iter()
    .filter(|x| (*x).1.len() != 0).map(|x| (x.0, x.1.into_iter()
        .filter(|x| re.is_match(x.as_str())).collect())).collect();

    for (key, val) in fechos.iter_mut() {
        let mut i: usize = 0;
        while i != val.len() {
            if let Some(key_val) = &val[i].chars().next() {
                if let Some(vector) = new_prod_rules.get(key_val){
                    if *key_val == *key {
                        i+=1;
                        continue;
                    }
                    val.pop();
                    val.append(&mut vector.to_owned());
                }
            }
            i+=1;
        }
    }

    fechos = fechos.into_iter().map(|(x, y)| (x, y.into_iter()
    .filter(|string| !re.is_match(&string.as_str()) && string != "").collect())).collect();

    fechos.into_iter().for_each(|(x, y)| {
        new_prod_rules.get_mut(&x).expect("")
            .append(&mut y.to_owned());
    });

    //Limpeza de variaveis que não podiam estar no vetor
    for (key, vector) in new_prod_rules.iter_mut() {
        let mut i : usize = 0;
        while i != vector.len() {
            if re.is_match(&vector[i].as_str()) && 
                vector[i] != key.to_string() {
                    vector.remove(i);
                    continue;
                }
            i+=1;
            }
        }

    return new_prod_rules;
}

fn cut_useless_prods(build_rules : &HashMap<char, Vec<String>>) -> HashMap<char, Vec<String>> {
    let prod_rules= remove_sub_prod(build_rules);
    let mut new_prod_rules: HashMap<char, Vec<String>> = HashMap::new();
    let re = Regex::new(r"[a-z&]").unwrap();
    let mut reachable_set = HashSet::<char>::new();
    reachable_set.insert('S');

    let mut vector = prod_rules.get(&'S').expect("Vector").to_owned();
    let mut i : usize = 0;
    while i != vector.len() {
        for string in re.split(&(vector[i].as_str().to_owned())) {
            for character in string.chars() {
                if let Some(vector_to_extend) = prod_rules.get(&character){
                    vector.extend(vector_to_extend.to_vec());
                    reachable_set.insert(character);
                }
            }
        }
        i+=1;
    }

    for key in reachable_set {
        if let Some(vector) = prod_rules.get(&key) {
            new_prod_rules.insert(key, vector.to_vec());
        }
    }

    return new_prod_rules;
}

fn convert_rules_to_chomsky(build_rules : &HashMap<char, Vec<String>>){
    let re = regex::Regex::new(r"^[a-z]$").unwrap();
    let mut converted_rules = build_rules.to_owned();
    let mut new_symbols = 'A';
    if let Some(start_vector) = converted_rules.get_mut(&'S') {
        for i in 0..start_vector.len(){
            if start_vector[i] == VOID_VAL {
                start_vector.remove(i);
                break;
            }
        }
    }


}

fn convert_rules_to_grebatch(){}