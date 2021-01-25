(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open System
open Prelude
open Microsoft.FSharp.Text
open SharpSolver.Impl

// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

let norm fmt = chout ConsoleColor.Yellow "norm" fmt
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt   
//aggiungo la funzione degree 
let degree1 fmt = chout ConsoleColor.DarkCyan "degree" fmt
// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input

        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing
            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)
            
            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni
            | Expr e1 -> let pol = reduce(e1)
                         let normal = normalize(pol)
                         redux "%O" pol
                         norm  "%O"  normal
                         //norm "%O" normal
                         degree1 "%d" (polynomial_degree(pol))
            | Equ (e1, e2) ->
                                let pol = reduce(e1) // riduco da espressione a polinomio
                                let pol2 = reduce(e2)
                                redux "%O = %O" pol pol2
                                // traformo il polinomio in un polinomio normalizzato
                                let normal = normalize pol
                                let normal2 = normalize pol2
                                // calcolo degree 
                                let degreeNormal1 = normalized_polynomial_degree normal
                                let degreeNormal2 = normalized_polynomial_degree normal2
                                // trovo il grado massimo
                                let mutable degreeMax = 0
                                if degreeNormal1 >= degreeNormal2 then degreeMax <- degreeNormal1 else degreeMax <- degreeNormal2
                                //unisco normal e normal2
                                //1) trasformo un polinomio normalizzato che `e formato da NormalizedPolynomial e un array di rational in un array
                                let normalToArray (NormalizedPolynomial(x)) = x
                                let array1 = normalToArray(normal)
                                let array2 = normalToArray(normal2)
                                // confronto la lunghezza degli array (non serve perchè abbiamo degreemax)
                                let mutable array3Lenght = 0
                                if (Array.length array1) >= (Array.length array2) then array3Lenght <- Array.length array1 else array3Lenght <- Array.length array2
                                if array3Lenght <> (degreeMax + 1) then printf "il grado non corrisponede" 
                                //3)creo un nuovo array
                                let mutable array3 = Array.init (degreeMax + 1) (fun _ -> (rational(0,1)))
                                //4) sommo all'array3 l 'array2 cambiato di segno
                                for i = 0 to ( Array.length array2 - 1 ) do
                                    array3.[i] <- (~-) array2.[i] 
                                //5) sommo all'array3 l'array1
                                for i = 0 to ( Array.length array1 - 1 ) do
                                    array3.[i] <- (array3.[i]) + (array1.[i]) 
                                //trasformo l'array3 in un polinomio normalizzato
                                let mutable normal3 = NormalizedPolynomial(array3)
                                //stamapa normal
                                //risolvo l'equazione

                                //semplifico
                                let mutable xzero = false                              
                                let semp = controllaGradoEffettivo normal3 // x2 - x2 = 0 léquazione non piu di secondo grado
                                normal3 <- semp 
                                norm "%O = 0"  normal3 
                                //una volta semplificato cambia il grado
                                degreeMax <- Array.length(normalToArray(normal3)) - 1
                                //stampa il grado
                                degree1 "%d" degreeMax
                                //controlla se il grado è maggiore = a 2
                                if degreeMax >= 2 
                                then 
                                    //controll se puó semplificare
                                    let normal4 = raccogli normal3 // raccoglimento totale
                                    //se è stata semplificata aggiunge x = 0 alle soluzioni
                                    if normal4 <> normal3 then xzero <- true 
                                    //controlla se il grado è cambiato
                                    degreeMax<- normalized_polynomial_degree normal4
                                    normal3 <- normal4
                                    array3 <- normalToArray(normal4)

                                if degreeMax = 0 
                                            then
                                                //chiama la funzione solve0 che risolve un equazione di grado 0
                                                let sol0 =solve0(normal3)
                                                ident "%O" sol0
                                            elif (degreeMax = 1) then  
                                                    //chiama la funzione solve1 che risolve un equazione di grado 1
                                                    let x1 =solve1(normal3)
                                                    //se è stata semplificata tramite raccoglimento totale allora aggiunge la soluzione x = 0
                                                    //stampa le soluzioni
                                                    if xzero = true 
                                                        then  sol "x1 = %i x2 = %O" 0 x1
                                                        else  sol "x = %O" x1
                                                        
                                            
                                            elif (degreeMax = 2) then                                              
                                                   let x2 =solve2(normal3)
                                                   //printfn "x2 solve2 = %O" x2
                                                   //stampa le soluzioni
                                                   match x2 with
                                                   | None            -> if (xzero = true) then sol "x = 0" else sol "%O" (None)

                                                   | Some (x1, None) -> if xzero = true then sol "x1 = %i x2 = %O " 0 x1
                                                                        else sol "x1 = %O " x1
                                                   | Some (x1, Some x2)  -> if xzero = true then sol "x1 = %i x2 = %O  x3 = %O " 0 x1 x2
                                                                            else sol "x1 = %O  x2 = %O " x1 x2

                                            elif (degreeMax = 3) then //porto l 'eq nella forma normale (senza termine con x2)
                                                                      let sempsolver = sempSolve3(normal3)
                                                                      hout "forma normale" "%O" sempsolver 
                                                                      //trova una soluizione
                                                                      let t1 = solve3(sempsolver)
                                                                      //printfn "sol: %f " t1
                                                                      let t2 = rationalize(t1)
                                                                      //printfn "sol: %O " t2
                                                                      //semplifica con ruffini 
                                                                      let ruf = ruffini (normal3) (t1)
                                                                      //printfn "eseguo ruffini: %O " ruf
                                                                      let rid (NormalizedPolynomial(x))  = x
                                                                      if (Array.length (rid(ruf))) = 3 
                                                                        then //risolvo l eq di 2 grado 
                                                                              let x2 =solve2(ruf)
                                                                              //printfn "x2 solve2 = %O" x2
                                                                              //stampa le soluzioni
                                                                              match x2 with
                                                                               | None            -> if (xzero = true) then sol "x1 = 0  x2 = %O" t2 else sol "x = %O" t2

                                                                               | Some (x1, None) -> if xzero = true then sol "x1 = %i x2 = %O x3 = %O " 0 t2 x1
                                                                                                    else sol "x1 = %O x2 = %O " t2 x1
                                                                               | Some (x1, Some x2)  -> if xzero = true then sol "x1 = %i x2 = %O  x3 = %O x4 = %O " 0 t2 x1 x2
                                                                                                        else sol "x1 = %O x2 = %O  x3 = %O " t2 x1 x2                                                                            

                                                                        else printfn "impossibile eseguire ruffini"
                                                                             if (xzero = true) then sol "x1 = 0  x2 = %O" t2 else sol "x = %O" t2

                                else       
                                printfn "grado superiore a 3" 

            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code


