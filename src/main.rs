use {regex::Regex, std::{collections::{HashMap, HashSet, VecDeque}, env, fs::{self}
, io::*, vec}};

const VOID_VAL : &str = "&";

fn main() {
    env::set_var("RUST_BACKTRACE", "1");
    let args: Vec<String> = env::args().collect();
    if args.len() < 2{
        panic!("Falta de argumentos"); 
    }
    let title_vector = vec!["simplified", "chomsky", "grebatch", "left_factor"];
    let prod_rules = get_build_rules(&args[1]);
    let rules = simplify_rules(&prod_rules);
    write_to_file_build_rule(&rules.0, title_vector[0]);
    write_to_file_build_rule(&rules.1, title_vector[1]);
    write_to_file_build_rule(&rules.2, title_vector[2]);
    write_to_file_build_rule(&rules.3, title_vector[3]);
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

fn simplify_rules(build_rules : &HashMap<String, Vec<String>>) -> (HashMap<String, Vec<String>>, HashMap<String, Vec<String>>, HashMap<String, Vec<String>>,  HashMap<String, Vec<String>>) {   
    let simplified_rules = clean_rules(&cut_useless_prods(build_rules));
    let chomsky_norm_rules = convert_rules_to_chomsky(&simplified_rules);
    let grebatch_norm_rules = convert_rules_to_grebatch(&simplified_rules);
    let deterministic_rules = make_left_fat_rules(&simplified_rules);
    return (simplified_rules, chomsky_norm_rules, grebatch_norm_rules, deterministic_rules);
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
    let split = Regex::new(r"([A-Z][0-9]*)").unwrap();
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

    for key in reachable_set.iter() {
        if let Some(vector) = prod_rules.get(&key.to_string()) {
            let mut new_vec = Vec::<String>::new();
            for string in vector.iter() {
                let mut add_in_vec = true;
                if let Some(capture) = split.captures(&string) {
                    if capture.len() != 1 {
                        for i in 1..capture.len() {
                            let value = capture.get(i).map_or("", |x| x.as_str());
                            if !reachable_set.contains(&value.to_string()) {
                                add_in_vec = false;
                                break;
                            }
                        }
                    }
                }
                if add_in_vec {
                    new_vec.push(string.to_string());
                }
            }
            new_prod_rules.insert(key.to_string(), new_vec.to_vec());
        }
    }

    return new_prod_rules;
}

fn clean_rules(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let mut cleaned_rules = HashMap::<String, Vec<String>>::new();
    for (key, vector) in build_rules.iter() {
        let mut new_vector = Vec::<String>::new();
        for string in vector {
            if new_vector.contains(string) {
                continue;
            }
            new_vector.push(string.to_string());
        }
        cleaned_rules.insert(key.to_string(), new_vector);
    }
    return cleaned_rules;
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
            let vetor : Vec<&str> = remove_first.split(&filtered_str).collect();
            if vetor.len() == 1 {
                continue;
            }
            let concat_string = format!("{}", vetor[1]);
            if let Some(first_char) = concat_string.chars().next(){
                let mut i: usize = 0;
                let mut new_key: String;
                new_key = format!("{first_char}{i}");
                while converted_rules.contains_key(&new_key) {
                    new_key = format!("{first_char}{i}");
                    i += 1;
                }
                converted_rules.insert(new_key.to_owned(), vec![concat_string.to_string()]);
                for rule in converted_rules.iter_mut() {
                    for x in rule.1.iter_mut() {
                        if *rule.0 != new_key {
                            *x = x.replace(&concat_string, &new_key);
                        }
                    }
                }
            }
        }
    }

    return converted_rules;
}

fn remove_left_recur(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let mut new_build_rules = build_rules.to_owned();
    let mut keys_to_go = VecDeque::<String>::new();
    let mut conversion_map = HashMap::<String, String>::new();
    let filter = regex::Regex::new(r"([A-Z][0-9]*)").unwrap();
    let mut index = 1;
    conversion_map.insert("S".to_string(), "S0".to_string());    

    for (key, vector) in  new_build_rules.iter_mut() {
        for string in vector {
            *string = string.replace("S", "S0");
            if key == "S" {
                if let Some(capture) = filter.captures(&string){
                    if capture.len() == 1 {
                        continue;
                    }
                    for i in 1..capture.len() {
                        if let Some(val) = capture.get(i).map_or(None, |x| Some(x.as_str().to_string())) {
                            if !keys_to_go.contains(&val)  && val != "S" {
                                keys_to_go.push_front(val);
                            }
                        }
                    }
                }
            }
        }
    }


    while !keys_to_go.is_empty() {
        if let Some(key_to_replace) = keys_to_go.pop_back() {
            let new_key = format!("S{index}");
            index += 1;
            conversion_map.insert(key_to_replace.to_string(), new_key.to_string());
            for (key, vect) in new_build_rules.iter_mut() {
                for string in vect {
                    *string = string.replace(&key_to_replace, &new_key);
                    if *key == key_to_replace {
                        if let Some(capture) = filter.captures(&string){
                            if capture.len() == 1 {
                                continue;
                            }
                            for i in 1..capture.len() {
                                if let Some(val) = capture.get(i).map_or(None, |x| Some(x.as_str().to_string())) {
                                    if !keys_to_go.contains(&val)  && !conversion_map.contains_key(&val) {
                                        keys_to_go.push_front(val.to_string());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    for (old_key, new_key) in conversion_map {
        if let Some(vector) = new_build_rules.get(&old_key) {
            new_build_rules.insert(new_key, vector.to_vec());
            new_build_rules.remove(&old_key);
        }
    }
    
    let mut copy_hash_map = new_build_rules.to_owned();
    let mut vector_to_append_later = Vec::<String>::new();

    for (key, vector) in new_build_rules.iter_mut() {
        let current_key_num = key.split("S").collect::<Vec<&str>>()[1].parse::<u32>().unwrap();
        *vector = vector.iter().filter(|x| !x.starts_with(key))
                .map(|x| x.to_string()).collect();
        for string in &mut *vector {
            if let Some(capture) = filter.captures(&string) {
                if let Some (key_matcher) = capture.get(1) {
                    let str_key = key_matcher.as_str();
                    let copy_key = str_key.to_string();
                    let number = str_key.split("S").collect::<Vec<&str>>()[1].parse::<u32>().unwrap();
                    if current_key_num <= number {
                        let vect_to_replace = copy_hash_map.get(str_key).unwrap();
                        let str_copy = string.to_owned();
                        *string = string.replacen(&str_key.to_string(), &vect_to_replace[0], 1);
                        for i in 1..vect_to_replace.len() {
                            vector_to_append_later.push(str_copy.replacen(&copy_key, &vect_to_replace[i], 1));
                        }
                        println!("{:?}", vector_to_append_later);
                    }
                }
            }
        }
        vector.append(&mut vector_to_append_later);
        for i in 0..vector_to_append_later.len() {
            vector_to_append_later.pop();
        }
    }
    
    return new_build_rules;
}

fn convert_rules_to_grebatch(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>>{
    let filter = regex::Regex::new(r"([A-Z][0-9]*)").unwrap();
    let mut converted_rules = remove_left_recur(&build_rules);
    let mut index = 0;
    *converted_rules.get_mut("S0").unwrap() = converted_rules.get("S0").unwrap().iter().filter(|x| **x != "&").map(|x| x.to_string()).collect();
    
    converted_rules.iter().for_each(|x| println!("{} {:?}", x.0, x.1));
    return converted_rules;
}

fn make_left_fat_rules(build_rules : &HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    let re = regex::Regex::new(r"([A-Z][0-9]*)").unwrap();
    let terminal_regex = regex::Regex::new(r"[a-z]").unwrap();
    let mut terminals = HashSet::<String>::new();
    let mut new_prod_rules = build_rules.to_owned();
    let mut index = 0;
    let mut dont_go_set = HashSet::<String>::new();
    let mut prod_to_add_later = HashMap::<String, Vec<String>>::new();

    for vetor in new_prod_rules.values() {
        for chars in vetor.iter().filter(|x| terminal_regex.is_match(&x)) {
            for str_char in chars.chars() {
                if str_char.is_ascii_lowercase() {
                    terminals.insert(str_char.to_string());
                }
            } 
        }
    }

    for terminal in terminals {
        index = 0;
        for (key, vetor) in new_prod_rules.iter_mut() {
            let new_key = format!("{key}{index}'"); 
            let mut new_vec = Vec::<String>::new();
            for string in vetor.iter_mut().filter(|x| x.len() > 1) {
                let split = string.to_owned();
                let (ini, resto) = split.split_at(1);
                if let Some(capture) = re.captures(resto){
                    if ini != terminal || capture.len()-1 == resto.len()-1 {
                        continue;
                    }
                    let new_str = string.replace(resto, &new_key);
                    *string = new_str;
                    new_vec.push(resto.to_string());
                }
            }
            let copy_key = new_key.to_owned();
            dont_go_set.insert(new_key);
            prod_to_add_later.insert(copy_key, new_vec.to_vec());
            index+=1;
        }
    } 

    prod_to_add_later.into_iter().for_each(|x| {
        if !x.1.is_empty() {
            new_prod_rules.insert(x.0, x.1);
        }
    });

    return new_prod_rules;
}

fn write_to_file_build_rule(build_rules : &HashMap<String, Vec<String>>, title_file : &str) {
    let mut file =  fs::File::create(format!("{title_file}.glc")).unwrap();
    for (key, vector) in build_rules.iter() {
        let _ = file.write_all(format!("{key}-> ").as_bytes());
        for i in 0..vector.len() {
            if i == vector.len()-1 {
                let _ = file.write_all(format!("{}\n", vector[i]).as_bytes());
            } else {
                let _ = file.write_all(format!("{} | ", vector[i]).as_bytes());
            }
        }
    }
}