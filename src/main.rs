use {regex::Regex, std::{collections::{HashMap, HashSet}, env, fs, string, vec}};

const VOID_VAL : &str = "&";

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2{
        panic!("Falta de argumentos"); 
    }
    let prod_rules = get_build_rules(&args[1]);
    let simplified_rules = simplify_rules(&prod_rules);
}

fn get_build_rules(file_path : &str) -> HashMap<String, Vec<String>> {
    let mut rules = HashMap::new();
    let string = fs::read_to_string(file_path).expect("ok");
    let split: Vec<&str> = string.split("\n").collect();
    for string in split{
        let vector: Vec<&str> = string.split("->").collect();
        let key = vector[0].trim().to_string();
        rules.insert(key, vector[1].split("|").map(|x| x.trim().to_string()).collect());
    }
    return rules;
}

fn simplify_rules(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {   
    let simplified_rule = cut_useless_prods(build_rules);
    let chomsky_norm_rules = convert_rules_to_chomsky(&simplified_rule);
    return simplified_rule;
}

fn remove_void(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let mut new_build_rules: HashMap<String, Vec<String>> = HashMap::new();
    let mut null_set = HashSet::<String>::new();
    let mut null_prev_size : usize;  
    for (k, vect) in build_rules{
        for val in vect {
            match (*val).cmp(&VOID_VAL.to_string()){
                std::cmp::Ordering::Greater => {},
                std::cmp::Ordering::Less => {},
                std::cmp::Ordering::Equal => {
                    null_set.insert(k.to_string());
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
                    null_set.insert(k.to_string());
                    for char in x.chars(){
                        if !null_set.contains(&char.to_string()){
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
        
        if *key == "S" && vect.into_iter().any(|x| x == &"&") {
            new_vect.push("&".to_string());
        } 
        
        for i in 0..new_vect.len() {
            for null_key in &null_set {
                if new_vect[i].contains(&*null_key){
                    let mut new_string = String::new();
                    let strings : Vec<String> = new_vect[i].split(&*null_key).map(|x| x.to_string()).collect();
                    new_string.push_str(&strings[0]);
                    new_string.push_str(&strings[1]);
                    if new_string.len() == 0 {
                        continue;
                    }
                    new_vect.push(new_string.trim().to_string());  
                }
            }
        }
        new_build_rules.insert(key.to_string(), new_vect);
    }

    return  new_build_rules;
}

fn remove_sub_prod(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let mut new_prod_rules = remove_void(build_rules);
    let re = Regex::new(r"^[A-Z]{1}$").unwrap();
    let mut fechos: HashMap<String, Vec<String>> = new_prod_rules.to_owned().into_iter()
    .filter(|x| (*x).1.len() != 0).map(|x| (x.0, x.1.into_iter()
        .filter(|x| re.is_match(x.as_str())).collect())).collect();

    for (key, val) in fechos.iter_mut() {
        let mut i: usize = 0;
        while i != val.len() {
            if let Some(key_val) = &val[i].chars().next() {
                if let Some(vector) = new_prod_rules.get(&key_val.to_string()){
                    if key_val.to_string() == *key {
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

fn cut_useless_prods(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let prod_rules= remove_sub_prod(build_rules);
    let mut new_prod_rules: HashMap<String, Vec<String>> = HashMap::new();
    let re = Regex::new(r"[a-z&]").unwrap();
    let mut reachable_set = HashSet::<String>::new();
    reachable_set.insert("S".to_string());

    let mut vector = prod_rules.get(&"S".to_string()).expect("Vector").to_owned();
    let mut i : usize = 0;
    while i != vector.len() {
        for string in re.split(&(vector[i].as_str().to_owned())) {
            for character in string.chars() {
                if let Some(vector_to_extend) = prod_rules.get(&character.to_string()){
                    vector.extend(vector_to_extend.to_vec());
                    reachable_set.insert(character.to_string());
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

fn convert_rules_to_chomsky(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let re = regex::Regex::new(r"^[a-zA-Z][a-z][A-Za-z]*$").unwrap();
    let split_re = regex::Regex::new(r"[A-Z][0-9]*").unwrap();
    let remove_first = regex::Regex::new(r"[a-z]").unwrap();
    let mut converted_rules = build_rules.to_owned();
    if let Some(start_vector) = converted_rules.get_mut(&"S".to_string()) {
        let mut i = 0;
        loop{
            if start_vector.len() == i{
                break;
            }
            if start_vector[i] == VOID_VAL {
                start_vector.remove(i);
                continue;
            }
            i+=1;
        }
    }

    for vector in converted_rules.to_owned().values(){
        for val in vector.to_vec().iter_mut().filter(|x| x.len() > 1
                && re.is_match(&x)){
            let tuple = val.split_at_mut(1);
            let splt = re.split(&tuple.1);
            for string in splt {
                let mut i: usize = 0;
                let mut new_key: String;
                let terminal = string.to_string();
                let formated_val = string.to_ascii_uppercase();
                new_key = format!("{formated_val}{i}");
                while converted_rules.contains_key(&new_key) {
                    new_key = format!("{formated_val}{i}");
                    i += 1;
                }
                converted_rules.insert(new_key.to_owned(), vec![terminal]);
                for rule in converted_rules.iter_mut() {
                    for x in rule.1.iter_mut() {
                        if *rule.0 != new_key {
                            *x = x.replace(&string, &new_key);
                        }
                    }
                }
            }
        }
    }

    for vector in converted_rules.to_owned().values().into_iter() {
        for filtered_str in vector.into_iter().filter(|x| x.len() > 2) {
            let slices : Vec<&str> = split_re.split(&filtered_str).collect();
            if slices.len() < 3 {
                continue;
            }
            let vector : Vec<&str> = remove_first.split(&filtered_str).collect();
            let concat_string = format!("{}", vector[1]);
            if let Some(first_char) = concat_string.chars().next(){
                let mut i = 0;
            }
        }
    }

    return converted_rules;
}

//fn convert_rules_to_grebatch(){}