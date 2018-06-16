-- will take a while to typecheck
ex = let f0 = \x -> (x,x) in
        let f1 = \y -> f0 (f0 y) in
            let f2 = \y -> f1 (f1 y) in
                let f3 = \y -> f2 (f2 y) in
                    let f4 = \y -> f3 (f3 y) in
                        f4 id
