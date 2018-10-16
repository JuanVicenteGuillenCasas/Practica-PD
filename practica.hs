--Juan Vicente Guillén Casas.
type Var = String 
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp deriving Read

--Instanciamos las tres clases que nos piden, x es igual a y si ambas expresiones son equivalentes, x es menor que y si y es consecuencia lógica de x,
-- y por último la clase show la instanciamos de manera recursiva para así identificar a todos los componentes de la expresión.
instance Eq FProp where
	x == y = equiv x y
instance Ord FProp where
	x < y = conseq y x
instance Show FProp where
	show(V v) = show v
	show(No f) = "~" ++ show f
	show(Y f g) = "(" ++ show f ++ ")  /\\  ("  ++ show g ++ ")"
	show(O f g) = "(" ++ show f ++ ")  \\/  ("  ++ show g ++ ")"
	show(Si f g) = "(" ++ show f ++ ")  ->  ("  ++ show g ++ ")"
	show(Sii f g) = "(" ++ show f ++ ")  <->  ("  ++ show g ++ ")" 

--Definimos 6 expresiones iniciales para así ahorrarnos trabajo en escribirlas todo el rato.
f1 =  Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
f2 =  Y (V "p") (Si (No (V "q")) (No (V "p")))
f3 =  Y ( Y (V "p") (V "q")) (O (No (V "q")) (V "r"))
f4 =  O (No (Y (V "p") ( No (V "r")))) (V "q")
f5 = Sii (No (O (V "r") (V "q"))) (Y (V "z") (V "p"))
f6 = Y (No (V "q")) (V "q")

--Definimos las funciones quickSort y Nub que la primera se encarga de ordenar una lista y la segunda de eliminar las repeticiones de una lista.
--Usaremos estas funciones para facilitarnos el trabajo.
quickSort::Ord a=>[a]->[a]
quickSort [] = []
quickSort (x:xs) = quickSort(menores) ++ [x] ++ quickSort(mayores)
	where
	menores = [y | y <-xs, y < x]
	mayores = [z | z <-xs, z >= x]

nub :: (Eq a) => [a] -> [a]
nub l = nub' l []
  where
    nub' [] _           = []
    nub' (x:xs) ls
        | x `elem` ls   = nub' xs ls
        | otherwise     = x : nub' xs (x:ls)

-- La función vars recibe una expresión y devuelve la lista sin repeticiones de las variables que aparecen en dicha expresión.
-- Está implementada de forma recursiva, de forma que va reconociendo componentes de la expresión tratando de buscar todas las variables posibles en éstos.
-- Siempre trata de reducirse todo a (V v) y esa variable meterla en la lista, la mayoría de funciones de esta practica funcionan así.		
vars:: FProp -> [Var]
vars f = quickSort (nub (vars2 f []))
	where
	vars2:: FProp -> [Var] -> [Var]
	vars2 (V v) ys = [v] ++ ys
	vars2 (No f) ys = vars2 f ys
	vars2 (Y f g) ys = (vars2 f []) ++ (vars2 g []) ++ ys
	vars2 (O f g) ys = (vars2 f []) ++ (vars2 g []) ++ ys
	vars2 (Si f g) ys = (vars2 f []) ++ (vars2 g []) ++ ys
	vars2 (Sii f g) ys = (vars2 f []) ++ (vars2 g []) ++ ys

--Para facilitarnos la vida tenemos esta función que dado un numero entero n, nos genera una tabla de la verdad para n variables.	
creaTabla:: Int -> [[Bool]]
creaTabla x = map (\x -> snd(x))(creaTabla2 x (map (\a -> (a, []))[0 .. (2^x - 1)]))
	where
	creaTabla2:: Int -> [(Int, [Bool])] -> [(Int, [Bool])]
	creaTabla2 0 xs = xs 
	creaTabla2 a xs = creaTabla2 (a - 1) (map (\x -> if mod (fst x) (2^a ) < 2^(a-1) then (fst x, False : snd x) else (fst x ,True : snd x) ) xs)

-- Básicamente es la función más importante de la practica, consta de 3 argumentos, el primero es la expresión a analizar, el segundo es la lista de variables
-- a la que la función puede acceder, la añadimos desde fuera debido a que en las funciones conseq y equiv vamos a necesitar ampliar la lista de variables para que se pueda
-- evaluar bien y obtener lo buscado y eso solo se puede hacer desde fuera, y el tercero la tabla de la verdad ajustada al numero de la lista de variables que nos entra.
-- Ahora el procedimiento es similar al de vars, forma recursiva ir simplificando hasta llegar a (V v) y una vez ahi buscamos en nuestra lista de variables la que se corresponda
-- con la v y vemos su posición en la tabla de la verdad, ese será su valor. Y luego es ir desplegandose y sacando el valor correspondiente.
eval:: FProp -> [Var] -> [Bool] -> Bool
eval (V v) (x:xs) (y:ys) = if v == x  then y else eval (V v) xs ys;
eval (No f) xs ys = not (eval f xs ys)
eval (Y f g) xs ys = (eval f xs ys) && (eval g xs ys)
eval (O f g) xs ys = (eval f xs ys) || (eval g xs ys)
eval (Si f g) xs ys = not (((eval f xs ys) == True) && ((eval g xs ys) == False ))
eval (Sii f g) xs ys =  (eval f xs ys) == (eval g xs ys)

-- Esta función recibe como parámetro una expresión y devuelve true o false en función de si es cierta o no para todos los valores posibles de sus variables.
-- Trata de usar un foldl (&&) con primer valor true e ir evaluando en cada valor de la tabla de la verdad, si hay alguno que haga que evalue falso gracias al foldl
-- sabemos que la función devolverá falso que es lo que nos piden. Si todas las evaluaciones son true nos devolverá true.
tau:: FProp -> Bool
tau f = foldl (&&) True [eval f (vars f) xy | xy <- (creaTabla (length (vars f)))]

-- Esta función recibe como parámetro una expresión y devuelve true si existe alguna combinación de valores para los cuales el evaluar sobre ellos la expresión dá true, y false si
-- para toda combinacion de valores devuelve false. Al contrario que la otra, esta usa foldl (||) False para así con encontrar un valor de la tabla de verdad que al evaluar
-- la expresión de true, la función pueda devolver true.
sat:: FProp -> Bool
sat f = foldl (||) False [eval f (vars f) xy | xy <- (creaTabla (length (vars f)))]

-- Esta función recibe dos expresiones f y g, en ese orden, y devuelve true si f es consecuencia lógica de g, es decir que si para ciertos valores g es cierto implica que f lo 
-- tiene que ser también, y devuelve false si esto no pasa. Ahora en la implementación de esta función tenemos que ver que no pase la situacion (ev f .. == false and ev g .. ==true)
-- para cierta combinación de valores, ya que si esto pasa tenemos que devolver false, si esto nunca pasa tendremos que f es consecuencia lógica de g y devolveremos true.
-- Tanto en esta función como en la siguiente tenemos que combinar las tablas de las variables para evitar obtener resultados erroneos y poder evaluar ambas funciones con la misma
-- combinación de valores todo el rato, y esta es la razón por la que la lista de variables se calcula antes de entrar a eval.
conseq:: FProp -> FProp -> Bool
conseq f g = foldl (&&) True [not (( eval f (nub(vars g ++ vars f)) ts == False) && (eval g (nub(vars g ++ vars f)) ts == True))| ts <- (creaTabla (length (nub(vars g ++ vars f))))]

-- Esta función recibe dos expresiones f y g, y devuelve true si son equivalentes, es decir que para todas las combinaciones de valores que haya tenemos que eval f == eval g.
-- La implementación es identica a la anterior, solo que en el recorrido tenemos que ver que siempre las evaluaciones coinciden. Si en un caso no coinciden devolveremos false,
-- pero si coinciden todas tendremos que son equivalentes y devolveremos true. Como en la anterior hay que combinar las tablas de variables de f y de g por el mismo motivo.
equiv:: FProp -> FProp -> Bool
equiv f g = foldl (&&) True [ (eval f (nub(vars g ++ vars f)) ts) == (eval g (nub(vars g ++ vars f)) ts)| ts <- (creaTabla (length (nub(vars g ++ vars f))))] 

-- Esta función recibe una lista de expresiones y devuelve una lista de listas de expresiones, la lista de la posición i contiene las expresiones de la lista que son consecuencia
-- lógica de la expresión i-ésima de la lista. Tratamos de ir recorriendo elemento a elemento la lista, en cada elemento sacamos las expresiones las cuales son consecuencia
-- lógica de dicho elemento, y así hasta acabar la lista.
consequenciasLista:: [FProp] -> [[FProp]]
consequenciasLista [] = []
consequenciasLista x = cs2 x x
	where 
	cs2:: [FProp] -> [FProp] -> [[FProp]]
	cs2 [] y = []
	cs2 (x:xs) (y) = [z | z <- y , conseq z x] : cs2 xs y

-- Esta función recibe una lista de expresiones y devuelve una lista con las clases de equivalencia haciendo el cociente con la función equiv. La implementación es idéntica
-- a la de la función anterior, ya que equiv es una función tipo relación equivalencia por lo que si dos elementos son equivalentes sus clases de equivalencia son la misma
-- luego usando nub nos quitamos los repetidos y llegamos al resultado.
equivalentesLista:: [FProp] -> [[FProp]]
equivalentesLista [] = []
equivalentesLista x = nub (e2 x x)
	where
	e2:: [FProp] -> [FProp] -> [[FProp]]
	e2 [] y = []
	e2 (x:xs) (y) = [z | z <- y, equiv x z] : e2 xs y

-- Para poder leer Int.
getInt:: IO Int 
getInt = do
	line <- getLine 
	return (read line :: Int)
-- Para poder leer FProp, necesario que FProp haga deriving de Read.
getFProp:: IO FProp 
getFProp = do
	line <- getLine 
	return (read line :: FProp)
-- Para poder leer [Bool], necesitaremos leer una lista de valores si estamos evaluando una formula.	
getListOfBool:: IO [Bool]
getListOfBool = do
	line <- getLine 
	return (read line :: [Bool])
	
--Pequeño menú de e-s que nos pedirá meter n fórmulasmen una lista y podremos elegir entre 5 opciones para hacer lo que queramos con ellas.
-- 1: Eliges 1 entre las n formulas y la evaluas con los valores que quieras.
-- 2: Eliges 1 entre las n formulas y comprueba si es tautología o no.
-- 3: Eliges 1 entre las n formulas y comprueba si es satisfactible o no.
-- 4: Ejecutamos la funcion consequenciasLista sobre nuestra lista de n formulas.
-- 5: Ejecutamos la funcion equivalentesLista sobre nuestra lista de n formulas.
main = do 
	putStrLn "Introduzca el numero de funciones: "
	n <- getInt 
	putStrLn "Introduzca las funciones que quieres mirar: "
	lista <- sequence [getFProp | i <- [1 .. n]]
	print (lista)
	putStrLn "Elige que quieres hacer: "
	putStrLn "1: Evaluar una de ellas."
	putStrLn "2: Ver si una de ella es tautología o no."
	putStrLn "3: Ver si una de ellas es satisfactible."
	putStrLn "4: Lista de consecuentes."
	putStrLn "5: Lista de equivalencias"
	putStr "Elijo: "
	s <- getInt
	if s == 1 then 
		do 
		putStrLn "Cual quieres evaluar? "
		j <- getInt
		putStrLn ("Inserte los valores que quiere ponerle a las variables " ++ show(vars (last (take j lista))) ++ " [False/True]: ")
		valors <- getListOfBool
		print (eval (last (take j lista)) (vars (last (take j lista))) valors)
	else if s == 2 then 
		do 
		putStrLn "Cual quieres comprobar si es tautología? "
		j <- getInt
		print (tau (last (take j lista)))
	else if s == 3 then 
		do 
		putStrLn "Cual quieres comprobar si es satisfactible? "
		j <- getInt
		print (sat (last (take j lista)))
	else if s == 4 then print (consequenciasLista lista)	
	else if s == 5 then print (equivalentesLista lista)
	else putStrLn "Tenias que haber elegido una de las anteriores!! "