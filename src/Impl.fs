
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System


//fun che prende un float e restituisce un rational
let rationalize (x : float) : rational = 
    //arrotnda x a 2 cifre dopo la virgola per wevitare blocchi
    let mutable s = Math.Round(x,2)  //crea una nuova variabile modificabile
    let mutable i = 0           //crea una variabile usata come contatore
    while (float(int(s))<s) do //confronta la parte intera con il numero originale
        s <- s*10.             //moltiplica il numero per 10
        i <- i+1                 //conta il numero di operazioni nel while
    let num = int(s)             //converte in int il valore
    let denom = int(10.0**float(i))  //calcola il denominatore come potenza di 10
    rational(num, denom)              // chiama la funzione rational


//restituisce il grado di un monomio
let monomial_degree (m : monomial) : int =  
    let monToInt (Monomial((_),x)) = x      //fun. che separa la parte intera del monomio
    monToInt(m)                             //chiama la funzione prima definita

//cambia segno ad un monomio
let monomial_negate (m : monomial) : monomial =  
    let monToRat (Monomial((s),_)) = s      //fun che separa la parte razionale
    let monToInt (Monomial((_),x)) = x      //fun che separa la parte intera
    let s = monToRat(m)                     //chiama la fun monToTat
    let x = monToInt(m)                     //chiama la fun. monToInt
    let parteRazionale1 = (~-) (s : rational)  //cambia il segno alla parte razionale
    Monomial((parteRazionale1),x)              //da in output il monomio cambiato di segno

// restituisce il grado di un polinomio
let polynomial_degree (p : polynomial) : int =  
        let i = 0                      // variabile usata per memorizzare il grado
        let rec aux p i =             // definisce una funzione ricorsiva aux
            match p with
            Polynomial[] -> i         //restituisce il grado se l'input è una lista vuota
            | Polynomial(x::xs) ->  if (monomial_degree(x) > i) then aux (Polynomial(xs)) (monomial_degree(x)) else aux (Polynomial(xs)) i    //se la testa x è di grado superiore ad i allora i = grado x
        aux p i  //esegue la funzione

// nega tutti i termini del polinomio
let polynomial_negate (p : polynomial) : polynomial = //funzione che prende un polinomio e restituisce il polinomio negato
        let rid (Polynomial(x)) = x   //funzione che restituisce una lista di monomi
        let x1 = rid(p)               // chiama la funzione rid    
        let rec nega x =              // funzione che data una lista di monomi nega ogni singolo monomio
            match x with
            [] -> []
            | x::xs -> monomial_negate(x)::nega(xs)                   
        Polynomial(nega(x1))   //restituisce il polinomio formato da Polinomial seguito dalla funzione nega applicata ad x1

// restituisce la il grado dell'array
let normalized_polynomial_degree (np : normalized_polynomial) : int =  
    let ridArray (NormalizedPolynomial(x)) = x   //ricava l'array dal tipo
    let  array1 = ridArray np                    //assegna ad array1 l'array 
    (Array.length (array1))-1                     //funzione che da in uscita la lunghezza dell'array 

// riordina un polinomio
let normalize (p : polynomial) : normalized_polynomial =        
   let reduceToMonomio (Polynomial(x)) = x
   let polinonomioRidotto = reduceToMonomio(p:polynomial)  //lista di monomi
   //calcola il grado massimo
   let len = polynomial_degree(p) 
   //inizializza l'array
   let mutable a = Array.init (len + 1) (fun _ -> (rational(0,1)))
   //scorre la lista di monomi
   let rec listMonomi list =
        match list with
        [] ->a
        | x::xs -> let gradoDelMonomio = monomial_degree (x)  // calcola il grado del monomio x
                   let riduciToRational (Monomial((x),_)) =  x //fun che ricava la parte razionale
                   let RationalNumber = riduciToRational(x)   // ricava la parte razionale
                   if (a.[gradoDelMonomio] = (rational(0,1))) then     //salva nel array
                            a.[gradoDelMonomio] <- RationalNumber       // sostituisce al valore 0 (0,1) la parte razionale 
                                                              else
                            let SumOfRationalNumber = (+) RationalNumber a.[gradoDelMonomio]  //somma al valore la nuova variabile
                            a.[gradoDelMonomio] <- SumOfRationalNumber  // sostiituisce il vecchio valore con la somma dei valori

                   listMonomi(xs)
   
   NormalizedPolynomial((listMonomi polinonomioRidotto))
   
//esegue la derivata di un polinomio 
let derive (p : polynomial) : polynomial =
    //trasformo il polinomio in una lista di monomi
    let reduceToMonomio (Polynomial(x)) = x  
    let mon1List = reduceToMonomio(p)           
    let rec modRat (lista : monomial list) lista2 =
            match lista with
            [] ->      lista2
            | x::xs -> //ricavo il grado e sottraggo 1
                       let gradodix = (monomial_degree(x))
                       //se il grado del monomio x è 0 allora il suo grado una volta derivato rimane 0
                       let mutable gradoDerivato = 0
                       if gradodix <> 0 then 
                            gradoDerivato <- gradodix-1
                       else
                            gradoDerivato <- 0
                       //ricavo la parte razionale dal monomio x (testa della lista)
                       let riduciARazionale (Monomial((x),_)) = x
                       let parteRazionale = riduciARazionale(x)
                       //moltiplico la parte razionale per il grado
                       let razionaleDerivated = (*) (parteRazionale) (rational(gradodix,1))
                       //riachiamo mon1list in ricorsione
                       //se il numero derivato è 0 allora non lo aggiungo alla lista
                       if (razionaleDerivated = (rational(0,1))) then modRat (xs) (lista2) 
                       else modRat (xs) ((lista2) @ ((Monomial(razionaleDerivated,gradoDerivato)::[])))                       
    Polynomial (modRat (mon1List) ([]))

//let mutable devoFareLaDerivata = false

//prende in input un expr e restituisce un polinomio, eseguendo le derivate se indicato
let reduce (e : expr) : polynomial = 
    let rec aux (e: expr) (cont: int) : polynomial = 
        match e with
        | Derive(D) -> aux (D) (cont + 1)   // incrementa di 1 count (n volte che deve fare la derivata)
        | Poly(S) -> if cont <> 0 then aux (Poly(derive(S))) (cont - 1)   //se count è diverso da 0 allora esegue la derivata e count diminuisce di 1
                     else S                                               // altrimenti da in output il polinmomio S
    aux e 0  //esegue la funzione aux , cont indica le n volte che deve derivare e parte da 0

//risolve un equazione di grado 0
let solve0 (np : normalized_polynomial) : bool =   // funzione che risolve l'equazioni di 0 grado
    let riduceToArray (NormalizedPolynomial(x)) = x  //funzione che prende un polinomio normalizzato e restituisce l'array di elementi
    let arr = riduceToArray (np)                     //richiama la funzione precedente
    let primoMenbro = arr.[0]                        //salva l'elemento 0 del'array
    if primoMenbro = (rational(0,1)) then true else false   //se primoMembro è 0 allora l'uguaglienza è vera altrimenti falsa
    
//risolve un equazione di grado 1
let solve1 (np : normalized_polynomial) : rational = 
    let riduceToArray (NormalizedPolynomial(x)) = x
    let arr = riduceToArray (np)
    let mutable primoMenbro = arr.[0]
    //(sposto il termine noto a destra e) cambio segno
    primoMenbro <- (~-) (primoMenbro) // cambia segno
    let mutable secondoMembro = arr.[1]  //termine con la x 
    //divido entrambi i membri per la parte davanti alla x
    primoMenbro <- primoMenbro / secondoMembro   
    //secondoMembro <- secondoMembro / secondoMembro   //risulta 1 rational(1,0)
    arr.[0] <- primoMenbro     // n
    //arr.[1] <- secondoMembro   // x
    arr.[0]                    //x = n 

//risolve un equazione di grado 2
let solve2 (np : normalized_polynomial) : (float * float option) option = 
    let riduceToArray (NormalizedPolynomial(x)) = x  //funzione che prende un polinomio normalizzato e ritorna un array di rational
    let arr = riduceToArray(np)  //richima la funzione precedente
    let c = arr.[0]    //c = elemnto di posizione 0 (termine noto)
    let b = arr.[1]    //b = elemento di posizione 1 (x)
    let a = arr.[2]    //a = elemento di posizione 2 (x2)
    //let discriminante = ((*) b b )- ((*)((*) (rational(4,1)) a) c) //calcola il delta
    let discriminante = (b * b) - ((rational(4,1))* a * c) //calcola il delta
    //printfn "delta = %O " discriminante
    if (( rational.op_Implicit(discriminante)) < ( rational.op_Implicit(rational(0,1)))) //converte in float il delta e controlla se è negativo
        then None 
        elif (discriminante = (rational(0,1))) then let r = ((/)((~-) b ) ((*) (rational(2,1)) a))
                                                    let r2 = rational.op_Implicit(r)
                                                    Some(r2,None)
        
        else let sqrDelta = (rational.Sqrt(discriminante))
             //printfn "sqrt = %O" sqrDelta
             let sqrDelta2 = System.Math.Round (sqrDelta,3)
             //printfn "sqrt2 = %F" sqrDelta2
             let ratioanlizeSqrDelta2 = rationalize (sqrDelta2)
             
             //let r2rp = (/)((+) ((~-) b) ratioanlizeSqrDelta2) ((*) (rational(2,1)) a)  // (- b + delta) /2a
             let calcoloSolPos = (((~-) b) + ratioanlizeSqrDelta2) / ((rational (2,1) ) *  a)  // (- b + delta) /2a
             let soluzionePositiva = rational.op_Implicit(calcoloSolPos)              //  salva come float
             let r2rn = (/)((-) ((~-) b) ratioanlizeSqrDelta2) ((*) (rational(2,1)) a)  // (- b - delta) / 2a
             let soluzioneNegativa =  rational.op_Implicit(r2rn)
             Some(soluzionePositiva,Some soluzioneNegativa)
             //None
           
//funzione che se non contiene il termine noto esegue il raccoglimento totale della x
let raccogli (np : normalized_polynomial) : normalized_polynomial =
        let rec raccoglimentoTotale (np : normalized_polynomial) : normalized_polynomial =
            let riduceToArray (NormalizedPolynomial(x)) = x
            let array = riduceToArray (np)
            let lunghezzaArray = Array.length array
            let mutable scomposizioneTotale = false
            // se il termine noto `e zero allora è possibile raccogliere
            if array.[0] = (rational(0,1)) then scomposizioneTotale <- true
            if scomposizioneTotale = true 
                then
                    array.[0] <- array.[lunghezzaArray - 1]
                    //creo un nuovo array di dimensione array - 1 contenente l'array semplificato
        
                    let array2 = Array.init (lunghezzaArray - 1) (fun _ -> (rational(0,1)) )
                    let lunghezzaArray2 = Array.length array2
                    for d = 0 to lunghezzaArray2 - 1 do 
                        array2.[d] <- array.[d + 1]
                    //rieseguo la funzione in ricorsione
                    raccoglimentoTotale(NormalizedPolynomial(array2))
                else
                    np  
            
        raccoglimentoTotale np
   
//controlla grado effettivo
let rec controllaGradoEffettivo  (np : normalized_polynomial) :normalized_polynomial = 
    let normalToArray (NormalizedPolynomial(x)) = x
    
    let mutable array = normalToArray np
    //stampa l'array
    //for i = 0 to Array.length array - 1 do
    //    printfn "%A" array.[i]
    let mutable lunghezzaArray = Array.length array
    if lunghezzaArray = 1 then np
    else
        if array.[lunghezzaArray - 1] = (rational(0,1))
            then
            //printfn "ok"
            let mutable newArray = Array.init (lunghezzaArray - 1 ) (fun _ -> (rational(0,1)))
            for i = 0 to Array.length newArray - 1 do 
                newArray.[i] <-  array.[i]
            controllaGradoEffettivo (NormalizedPolynomial(newArray))
            else    
            np

//eq di terzo grado formula di Cardano

let mutable bterzi = 0.

//variabile che mi occorre in altre funzioni
//funzione che trasforma un equazione di terzo grado nella forma t3 + pt + q = 0
//sostituisco la x con t - b/3
let sempSolve3 (np : normalized_polynomial) : normalized_polynomial = //equazione ridotta alla forma normale 
    let rid (NormalizedPolynomial(x)) = x
    let arr = rid(np)
    let a = arr.[3]
    let b = arr.[2]
    let c = arr.[1]
    let d = arr.[0]
    let arr2 = Array.init (4) (fun _ -> (rational(0,1))) //crea un nuovo array
    let mutable a2 = arr2.[3]
    let mutable b2 = arr2.[2]
    let mutable c2 = arr2.[1]
    let mutable d2 = arr2.[0]
    //printfn "passaggio 0"
    //variabile che mi occorre in altre funzioni
    bterzi <- rational.op_Implicit (b/(rational(3,1)))
    //sostituisco x con  t - b/3
    a2 <- ((~-) (b/(rational(3,1)))) // * a
    b2 <- ((~-) (b/(rational(3,1)))) // * b
    c2 <- ((~-) (b/(rational(3,1)))) // * c
    d2 <- d
    //printfn "passaggio 1"
    //eseguo il cubo di a2
    let cuboDia2 = Array.init (4) (fun _ -> (rational(0,1))) //crea un nuovo array
    let mutable a2a = cuboDia2.[3]
    let mutable b2a = cuboDia2.[2]
    let mutable c2a = cuboDia2.[1]
    let mutable d2a = cuboDia2.[0]
    a2a <- (rational(1,1))  * a // * t3
    b2a <- ((rational(3,1)) * a2)  * a // * t2
    c2a <- ((rational(3,1)) * (a2 * a2)) * a // * t
    d2a <- (a2 * a2 * a2) * a  //grado 0
    //printfn "passaggio 2"
    //eseguo il quadrato di b2
    let quadroDib2 = Array.init (3) (fun _ -> (rational(0,1))) 
    let mutable a2b = arr2.[2]
    let mutable b2b = arr2.[1]
    let mutable c2b = arr2.[0]
    a2b <- (rational(1,1)) * b // * t2
    b2b <- ((rational(2,1)) * b2) * b // * t
    c2b <- (b2 * b2) * b
    //printfn "passaggio 3"
    //c * (t - c2
    let moltC2 = Array.init (2) (fun _ -> (rational(0,1))) 
    let mutable a2c = arr2.[1]
    let mutable b2c = arr2.[0]
    a2c <- c
    b2c <- c2 * c
    //printfn "passaggio 4"
    //d2 termine senza x rimane d2
    //sommo i termini simili 
    let somma = Array.init (4) (fun _ -> (rational(0,1))) 
    somma.[0] <-  b2c + c2b + d2a + d2
    somma.[1] <-  a2c + b2b + c2a
    somma.[2] <-  a2b + b2a
    somma.[3] <-  a2a
    NormalizedPolynomial(somma)

//risolve un eq di grado 3 con il metodo di cardano
let solve3 (np : normalized_polynomial) =
    let rid (NormalizedPolynomial(x)) = x
    let arr = rid(np)
    let a = arr.[3]
    let b = arr.[2]
    let c = arr.[1]
    let d = arr.[0]
    //definisco p e q  (t3 + pt + q = 0)
    let p = c
    let q = d
    let q1 = rational.op_Implicit(q)
    //calcola il determinante 
    let qmezzi = (q / (rational(2,1)))
    let delta = let pterzi = (p / (rational(3,1)))
                (qmezzi * qmezzi) + (pterzi * pterzi * pterzi)
    //printfn "deltasolve3 = %O" delta 
    let deltaFloat = rational.op_Implicit (delta)
    //controlla se il discriminante è positivo
    if deltaFloat > 0. 
    then 
        //printfn " passaggio 5"
        // t1 = u1 + u2  u12 = radicecubica(-(q/2) +- radiceq delta)
        //calcola la radice quadrata del discriminante 
        let radiceQuadraDelta = Math.Pow(deltaFloat, 0.5)
        //arrotonda a cinque cifre il risultato
        let radiceQuadrataDelta = System.Math.Round (radiceQuadraDelta,5)
        // cambia segno a qmezzi e converte in float
        let qmezziNegato = rational.op_Implicit(((~-) qmezzi)) 
        //calcola u1
        let mutable qmezziPiuRadDelta = qmezziNegato + radiceQuadrataDelta
        //calcola u2
        let mutable qmezziMenoRadDelta = qmezziNegato - radiceQuadrataDelta
        //printfn " passaggio 6"
        //cambia segno prima della radice se negativo: risolvo problema NaN
        let mutable q1Negativo = false
        let mutable q2Negativo = false
        if (qmezziPiuRadDelta >= 0.) then q1Negativo <- false 
           else 
           qmezziPiuRadDelta <- qmezziPiuRadDelta * -1.
           q1Negativo <- true
        if (qmezziMenoRadDelta >= 0.) then q2Negativo <- false 
           else 
           qmezziMenoRadDelta <- qmezziMenoRadDelta * -1.
           q1Negativo <- true
        //arrotnda qmezziPiuDelta e calcola la radice cubica 1/3 = 0.333333 
        let u1b = Math.Pow(qmezziPiuRadDelta, 0.33333)
        let mutable u1 = System.Math.Round (u1b,5)
        let u2b = Math.Pow((qmezziMenoRadDelta), 0.33333)
        let mutable u2 = System.Math.Round (u2b,5)
        //printfn " passaggio 7"
        //metto a posto il segno cambiato precedentemente
        if (q1Negativo = true) then u1 <- u1 * -1.
        if (q2Negativo = true) then u2 <- u2 * -1.
        let t1b = u1 + u2
        let t1 = System.Math.Round (t1b,5)
        //printfn "sol t1 = %f" t1
        let xsol = t1 - bterzi
        let xf =Math.Round (xsol,4)
        xf
        // trovata la prima soluzione ora si abbassa il grado
    elif(deltaFloat < 0.) 
        then 
        //calcola angolo alfa 
        //alfa = cosalfa = -qmezzi / (radcubica((|p| / 3)^3))
        //calcola -qmezzi
        //printfn " passaggio 8"
        
        let qmezzi1 = (q1/2.) * -1.
        //calcola il valore assouluto di p
        let mutable valp = rational.op_Implicit(p) //converte p in float
        if (valp < 1.) then valp <- valp * -1.  //cambio segno (valore assouluto)
        //divide valp per tre
        let valpTerzi = valp / 3.
        //eleva alla terza
        let valpTerziElevatoA3 = Math.Pow (valpTerzi, 3.)
        //printfn " passaggio 9"
        //esegue la radice quadrata
        let radiceDiVal = Math.Sqrt(valpTerziElevatoA3)
        //arrotonda
        let radiceDiVal2 = System.Math.Round(radiceDiVal,5)
        //- qmezzi / radiceDiVal2
        let cosalfa = qmezzi1 / radiceDiVal2
        //printfn " passaggio 10"
        //calcolo alfa eseguendo arcoos
        let acos = Math.Acos(cosalfa)
        let convertiInGradi (rad:float) :float = (rad * 180.) / 3.14159
        let acos1 = convertiInGradi(acos)  //trovato alfa
        let alfaterzi2 = acos1/3.
        let alfaterzi = System.Math.Round(alfaterzi2,5)
        //printfn " passaggio 11"
        //x1 = 2 * sqrt(|b| / 3)  * cos(alfa/3)
        let ptosqrt = valpTerzi
        //eseguo la radice
        let radicedip = Math.Sqrt(valpTerzi)
        //moltiplico per 2
        let radic2v = 2. * radicedip
        //eseguo il coseno di alfaterzi
        //let cosdiAlfaTerzi = Math.Cos(convertiInGradi(alfaterzi))
        //converto alfa terzi in radianti
        //math fa le conversioni da radianti
        let alfaradianti = (3.14159 * alfaterzi) / 180.
        let cosdiAlfaTerzi = Math.Cos(alfaradianti)
        //printfn "coseno =  %f" cosdiAlfaTerzi
        let fine = radic2v * cosdiAlfaTerzi
        let x1 = fine
        //printfn " passaggio 12"
        let x = Math.Round((x1 - bterzi),4)
        x
     else 
        //delta = 0 
        //t1 = u1 + v
        let mutable qmezzi2 = (q1/2. ) * -1.
        //printfn "qmezzi2= %f" qmezzi2
        let mutable negato = false
        if qmezzi2 < 0. 
            then 
            negato <- true
            qmezzi2 <- qmezzi2 * -1.
        let mutable u1 = Math.Pow(qmezzi2,0.33333)
        if negato = true then u1 <- u1 * -1.
        //printfn "u1= %f" u1
        let t1 = Math.Round( (u1 + u1) , 4)
        let x = Math.Round((t1 - bterzi),4)
        x

// funzione che semplifica con la regola di ruffini un equazione di terzo grado conoscendo una sua soluzione
let ruffini (eq : normalized_polynomial) (x1:float): normalized_polynomial =
    //la funzione prende in input solo polinomi di grado 3
    //definisco i membri dell 'equazione
    let rid (NormalizedPolynomial(x)) = x
    let arr = rid(eq)
    let a = arr.[3]
    let b = arr.[2]
    let c = arr.[1]
    let d = arr.[0]
    //definisco un nuovo array result
    let result = Array.init (4) (fun _ -> (0.0 :double )) //crea un nuovo array
    //printfn " passaggio 13"
    let x = x1
    //eseguo i calcoli
    result.[3] <- rational.op_Implicit(a)
    result.[2] <- (result.[3] * x) + (rational.op_Implicit(b))
    result.[1] <- (result.[2] * x) + (rational.op_Implicit(c))
    result.[0] <- ((result.[1] * x) + (rational.op_Implicit(d)))
    //printfn " passaggio 14"
    let grado0 = Math.Round(result.[0])
    if grado0 = 0.
        then
        //printfn " passaggio 15"
        //definisco un nuovo array result
        let result2 = Array.init (3) (fun _ -> (rational(0,1)))
        result2.[0] <- rationalize(Math.Round ((result.[1]),5))
        result2.[1] <- rationalize(Math.Round ((result.[2]),5))
        result2.[2] <- rationalize(Math.Round ((result.[3]),5))
        //printfn " passaggio 16"
        (NormalizedPolynomial(result2))
    else eq




