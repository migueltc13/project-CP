\documentclass[11pt, a4paper, fleqn]{article}
\usepackage{cp2425t}
\makeindex

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (Seq (a)) = "{" a "}^{*}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\," g "\,\ranabracket"
%format (anaRose (g)) = "\lanabracket\," g "\,\ranabracket_\textit{\tiny R}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloRose (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny R}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
%format (square (x)) = x "^2"

%format (cataTree (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny T}}"
%format (cataForest (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny F}}"
%format (anaTree (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny T}}"
%format (anaForest (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny F}}"
%format (hyloTree (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny T}}"
%format (hyloForest (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny F}}"
%format inTree = "\mathsf{in}_{Tree}"
%format inForest = "\mathsf{in}_{Forest}"
%format outTree = "\mathsf{out}_{Tree}"
%format outForest = "\mathsf{out}_{Forest}"

%format (cata' (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis"
%format (ana' (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket"
%format (hylo' (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket"
%format .* = "\star "
%format (hyloList (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"

%------------------------------------------------------------------------------%


%====== DEFINIR GRUPO E ELEMENTOS =============================================%

\group{7}
\studentA{95485}{Miguel Torres Carvalho}
\studentB{96587}{Flávia Alexandra da Silva Araújo}
\studentC{104001}{Frederico Cunha Afonso}

%==============================================================================%

\begin{document}

\sffamily
\setlength{\parindent}{0em}
\emergencystretch 3em
\renewcommand{\baselinestretch}{1.25}
\input{Cover}
\pagestyle{pagestyle}
\setlength{\parindent}{1em}
\newgeometry{left=25mm,right=20mm,top=25mm,bottom=25mm}

\section*{Preâmbulo}

Em \CP\ pretende-se ensinar a progra\-mação de computadores como uma disciplina
científica. Para isso parte-se de um repertório de \emph{combinadores} que
formam uma álgebra da programação % (conjunto de leis universais e seus corolários)
e usam-se esses combinadores para construir programas \emph{composicionalmente},
isto é, agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm esta disciplina,
opta-se pela aplicação deste método à programação em \Haskell\ (sem prejuízo
da sua aplicação a outras linguagens funcionais). Assim, o presente trabalho
prático coloca os alunos perante problemas concretos que deverão ser implementados
em \Haskell. Há ainda um outro objectivo: o de ensinar a documentar programas,
a validá-los e a produzir textos técnico-científicos de qualidade.

Antes de abordarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao \emph{software} a instalar, etc.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções simples
e elegantes que utilizem os combinadores de ordem superior estudados na disciplina.

%if False
\begin{code}
{-# LANGUAGE NPlusKPatterns, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Main where
import Cp
import List hiding (fac)
import Nat hiding (aux)
import LTree
import FTree
import Exp
-- import Probability
import Data.List hiding (find)
-- import Svg hiding (for,dup,fdiv)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
import Data.Char
import Data.Ratio
import Control.Concurrent
import Data.Time (UniversalTime)

main = undefined
\end{code}
%endif

\Problema

Esta questão aborda um problema que é conhecido pela designação '\emph{H-index of a Histogram}'
e que se formula facilmente:
\begin{quote}\em
O h-index de um histograma é o maior número |n| de barras do histograma cuja altura é maior ou igual a |n|.
\end{quote}
Por exemplo, o histograma
\begin{code}
h = [5,2,7,1,8,6,4,9]
\end{code}
que se mostra na figura
	\histograma
tem |hindex h = 5|
pois há |5| colunas maiores que |5|. (Não é |6| pois maiores ou iguais que seis só há quatro.)

Pretende-se definida como um catamorfismo, anamorfismo ou hilomorfismo uma função em Haskell
\begin{code}
hindex :: [Int] -> (Int,[Int])
\end{code}
tal que, para |(i,x) = hindex h|, |i| é o H-index de |h| e |x| é a lista de colunas de |h| que para ele contribuem.

A proposta de |hindex| deverá vir acompanhada de um \textbf{diagrama} ilustrativo.

\Problema

Pelo \href{https://en.wikipedia.org/wiki/Fundamental_theorem_of_arithmetic}{teorema
fundamental da aritmética}, todo número inteiro positivo tem uma única factorização
prima.  For exemplo,
\begin{verbatim}
primes 455
[5,7,13]
primes 433
[433]
primes 230
[2,5,23]
\end{verbatim}

\begin{enumerate}

\item
Implemente como anamorfismo de listas a função
\begin{code}
primes :: Integer -> [Integer]
\end{code}
que deverá, recebendo um número inteiro positivo, devolver a respectiva lista
de factores primos.

A proposta de |primes| deverá vir acompanhada de um \textbf{diagrama} ilustrativo.

\item A figura mostra a ``\emph{árvore dos primos}'' dos números |[455,669,6645,34,12,2]|.

      \primes

Com base na alínea anterior, implemente uma função em Haskell que faça a
geração de uma tal árvore a partir de uma lista de inteiros:

\begin{code}
prime_tree :: [Integer] -> Exp Integer Integer
\end{code}

\textbf{Sugestão}: escreva o mínimo de código possível em |prime_tree| investigando
cuidadosamente que funções disponíveis nas bibliotecas que são dadas podem
ser reutilizadas.%
\footnote{Pense sempre na sua produtividade quando está a programar --- essa
atitude será valorizada por qualquer empregador que vier a ter.}

\end{enumerate}

\Problema

A convolução |a .* b| de duas listas |a| e |b| --- uma operação relevante em computação
---  está muito bem explicada
\href{https://www.youtube.com/watch?v=KuXjwB4LzSA}{neste vídeo} do canal
\textbf{3Blue1Brown} do YouTube,
a partir de \href{https://www.youtube.com/watch?v=KuXjwB4LzSA&t=390s}{|t=6:30|}.
Aí se mostra como, por exemplo:
\begin{quote}
|[1,2,3] .* [4,5,6] = [4,13,28,27,18]|
\end{quote}
A solução abaixo, proposta pelo chatGPT,
\begin{spec}
convolve :: Num a => [a] -> [a] -> [a]
convolve xs ys = [sum $ zipWith (*) (take n (drop i xs)) ys | i <- [0..(length xs - n)]]
  where n = length ys
\end{spec}
está manifestamente errada, pois |convolve [1,2,3] [4,5,6] = [32]| (!).

Proponha, explicando-a devidamente, uma solução sua para |convolve|.
Valorizar-se-á a economia de código e o recurso aos combinadores \emph{pointfree} estudados
na disciplina, em particular a triologia \emph{ana-cata-hilo} de tipos disponíveis nas
bibliotecas dadas ou a definir.

\Problema

Considere-se a seguinte sintaxe (abstrata e simplificada) para \textbf{expressões numéricas} (em |b|) com variáveis (em |a|),
\begin{code}
data Expr b a =   V a | N b | T Op [ Expr b a ]  deriving (Show,Eq)

data Op = ITE | Add | Mul | Suc deriving (Show,Eq)
\end{code}
possivelmente condicionais (cf.\ |ITE|, i.e.\ o operador condicional ``if-then-else``).
Por exemplo, a árvore mostrada a seguir
        \treeA
representa a expressão
\begin{eqnarray}
        |ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))|
        \label{eq:expr}
\end{eqnarray}
--- i.e.\ |if x then 0 else y*(3+y)| ---
assumindo as ``helper functions'':
\begin{code}
soma  x y = T Add [x,y]
multi x y = T Mul [x,y]
ite x y z = T ITE [x,y,z]
\end{code}

No anexo \ref{sec:codigo} propôe-se uma base para o tipo Expr (|baseExpr|) e a
correspondente algebra |inExpr| para construção do tipo |Expr|.

\begin{enumerate}
\item        Complete as restantes definições da biblioteca |Expr|  pedidas no anexo \ref{sec:resolucao}.
\item        No mesmo anexo, declare |Expr b| como instância da classe |Monad|. \textbf{Sugestão}: relembre os exercícios da ficha 12.
\item        Defina como um catamorfismo de |Expr| a sua versão monádia, que deverá ter o tipo:
\begin{code}
mcataExpr :: Monad m => (Either a (Either b (Op, m [c])) -> m c) -> Expr b a -> m c
\end{code}
\item        Para se avaliar uma expressão é preciso que todas as suas variáveis estejam instanciadas.
Complete a definição da função
\begin{code}
let_exp :: (Num c) => (a -> Expr c b) -> Expr c a -> Expr c b
\end{code}
que, dada uma expressão com variáveis em |a| e uma função que a cada uma dessas variáveis atribui uma
expressão (|a -> Expr c b|), faz a correspondente substituição.\footnote{Cf.\ expressões |let ... in ...|.}
Por exemplo, dada
\begin{code}
f "x" = N 0
f "y" = N 5
f _   = N 99
\end{code}
ter-se-á
\begin{spec}
        let_exp f e = T ITE [N 1,N 0,T Mul [N 5,T Add [N 3,N 1]]]
\end{spec}
isto é, a árvore da figura a seguir:
        \treeB

\item Finalmente, defina a função de avaliação de uma expressão, com tipo

\begin{code}
evaluate :: (Num a, Ord a) =>  Expr a b -> Maybe a
\end{code}

que deverá ter em conta as seguintes situações de erro:

\begin{enumerate}

\item \emph{Variáveis} --- para ser avaliada, |x| em |evaluate x| não pode conter variáveis. Assim, por exemplo,
        \begin{spec}
        evaluate e = Nothing
        evaluate (let_exp f e) = Just 40
        \end{spec}
para |f| e |e|  dadas acima.

\item \emph{Aridades} --- todas as ocorrências dos operadores deverão ter
      o devido número de sub-expressões, por exemplo:
        \begin{spec}
        evaluate (T Add [ N 2, N 3]) = Just 5
        evaluate (T Mul [ N 2 ]) = Nothing
        \end{spec}

\end{enumerate}

\end{enumerate}

\noindent
\textbf{Sugestão}: de novo se insiste na escrita do mínimo de código possível,
tirando partido da riqueza estrutural do tipo |Expr| que é assunto desta questão.
Sugere-se também o recurso a diagramas para explicar as soluções propostas.

\part*{Anexos}

\appendix

\section{Natureza do trabalho a realizar}
\label{sec:documentacao}
Este trabalho teórico-prático deve ser realizado por grupos de 3 alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo em \textbf{todos}
os exercícios do trabalho, para assim poderem responder a qualquer questão
colocada na \emph{defesa oral} do relatório.

Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita ``\litp{literária}'' \cite{Kn92}, cujo
princípio base é o seguinte:
%
\begin{quote}\em
	Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o \textbf{código fonte} e a \textbf{documentação} de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2425t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2425t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no \MaterialPedagogico\
desta disciplina des\-com\-pactando o ficheiro \texttt{cp2425t.zip}.

Como se mostra no esquema abaixo, de um único ficheiro (|lhs|)
gera-se um PDF ou faz-se a interpretação do código \Haskell\ que ele inclui:

	\esquema

Vê-se assim que, para além do \GHCi, serão necessários os executáveis \PdfLatex\ e
\LhsToTeX. Para facilitar a instalação e evitar problemas de versões e
conflitos com sistemas operativos, é recomendado o uso do \Docker\ tal como
a seguir se descreve.

\section{Docker} \label{sec:docker}

Recomenda-se o uso do \container\ cuja imagem é gerada pelo \Docker\ a partir do ficheiro
\texttt{Dockerfile} que se encontra na diretoria que resulta de descompactar
\texttt{cp2425t.zip}. Este \container\ deverá ser usado na execução
do \GHCi\ e dos comandos relativos ao \Latex. (Ver também a \texttt{Makefile}
que é disponibilizada.)

Após \href{https://docs.docker.com/engine/install/}{instalar o Docker} e
descarregar o referido zip com o código fonte do trabalho,
basta executar os seguintes comandos:
\begin{Verbatim}[fontsize=\small]
    $ docker build -t cp2425t .
    $ docker run -v ${PWD}:/cp2425t -it cp2425t
\end{Verbatim}
\textbf{NB}: O objetivo é que o container\ seja usado \emph{apenas}
para executar o \GHCi\ e os comandos relativos ao \Latex.
Deste modo, é criado um \textit{volume} (cf.\ a opção \texttt{-v \$\{PWD\}:/cp2425t})
que permite que a diretoria em que se encontra na sua máquina local
e a diretoria \texttt{/cp2425t} no \container\ sejam partilhadas.

Pretende-se então que visualize/edite os ficheiros na sua máquina local e que
os compile no \container, executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2425t.lhs > cp2425t.tex
    $ pdflatex cp2425t
\end{Verbatim}
\LhsToTeX\ é o pre-processador que faz ``pretty printing'' de código Haskell
em \Latex\ e que faz parte já do \container. Alternativamente, basta executar
\begin{Verbatim}[fontsize=\small]
    $ make
\end{Verbatim}
para obter o mesmo efeito que acima.

Por outro lado, o mesmo ficheiro \texttt{cp2425t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2425t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2425t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Em que consiste o TP}

Em que consiste, então, o \emph{relatório} a que se referiu acima?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2425t.aux
    $ makeindex cp2425t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. (Como já se disse, pode fazê-lo
correndo simplesmente \texttt{make} no \container.)

No anexo \ref{sec:codigo} disponibiliza-se algum código \Haskell\ relativo
aos problemas que são colocados. Esse anexo deverá ser consultado e analisado
à medida que isso for necessário.

Deve ser feito uso da \litp{programação literária} para documentar bem o código que se
desenvolver, em particular fazendo diagramas explicativos do que foi feito e
tal como se explica no anexo \ref{sec:diagramas} que se segue.

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2TeX} \label{sec:diagramas}

Como primeiro exemplo, estudar o texto fonte (\lhstotex{lhs}) do que está a ler\footnote{
Procure e.g.\ por \texttt{"sec:diagramas"}.} onde se obtém o efeito seguinte:\footnote{Exemplos
tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
|
	id = split f g
|
\just\equiv{ universal property }
|
     lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )
|
\just\equiv{ identity }
|
     lcbr(
          p1 = f
     )(
          p2 = g
     )
|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \Xymatrix, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
h :: [Int]
\end{code}

\subsection*{Problema 4}
Definição do tipo:
\begin{code}
inExpr = either V (either N (uncurry T))

baseExpr g h f = g -|- (h -|- id >< map f)
\end{code}
Exemplos de expressões:
\begin{code}
e = ite (V "x") (N 0) (multi (V "y") (soma (N 3) (V "y")))
i = ite (V "x") (N 1) (multi (V "y") (soma (N (3%5)) (V "y")))
\end{code}
Exemplo de teste:
\begin{code}
teste = evaluate (let_exp f i) == Just (26 % 245)
    where f "x" = N 0 ; f "y" = N (1%7)
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}

\subsection*{Problema 1}

\begin{quote}\em
O \textit{h-index} de um histograma é o maior número |n| de barras do histograma cuja
altura é maior ou igual a |n|.
\end{quote}

Para a resolução deste problema, recorreu-se a uma estratégia de divisão e conquista
com recurso a um hilomorfismo de listas, definido na biblioteca \List,
com o anamorfismo responsável por ordenar a lista de \textit{input} de forma crescente
e o catamorfismo que, iterativamente, seleciona os elementos, incrementando o valor de \textit{h-index},
em que |n| corresponde aos |n| elementos maiores ou iguais a |n|, sendo esta condição
um invariante ao longo das iterações do catamorfismo. Graças à forma recursiva do catamorfismo,
dada pelo functor do catamorfismo |conquer|, é possível iterar sobre a lista de forma
decrescente, garantindo que o valor de \textit{h-index} é o maior possível.

A estrutura de dados intermédia deste hilomorfismo é uma lista de inteiros,
do tipo |[Int]|, esta correspondendo à saída do anamorfismo |divide| e à
respetiva entrada do catamorfismo |conquer|.

\includegraphics[width=.9\textwidth]{cp2425t_media/hindex-hylo.png}

\begin{code}
hindex = hyloList conquer divide
  where
    conquer = either g1 g2
    g1 = const (0, [])
    g2 (h, t@(i, x))
      | h > i     = (i+1, h:x)
      | otherwise = t

    divide [] = i1 ()
    divide xs = let m = minimum xs
                in i2 (m, delete m xs)
\end{code}

\clearpage

Para além da solução apresentada, foi também desenvolvida uma solução alternativa
que recorre somente a um catamorfismo de listas, modificado de forma a que a função
|out| seja capaz, aquando a lista de entrada não é vazia, de dividir a lista em
duas partes, uma com o valor mínimo e outra com o restante da lista. Deste modo,
a funcionalidade do anamorfismo |divide| é incorporada na função |out|.

A seguinte solução alternativa é 100\% \textit{pointfree}, com a função |g2| do gene
do catamorfismo redesenhada, assim como a função |out|, esta, como supramencionado,
equivalente à função |divide| da solução principal.

\includegraphics[width=.8\textwidth]{cp2425t_media/hindex-cata.png}

\begin{code}
hindex' :: [Int] -> (Int, [Int])
hindex' = cata conquer
  where
    conquer = either g1 g2
    g1 = const (0, [])
    g2 = cond (uncurry (>) . (id >< p1))
              (split (succ . p1 . p2) (cons . (id >< p2)))
              p2

outSortList = cond ([] ==)
                   (i1 . (!))
                   (i2 . split p1 (uncurry delete) . split minimum id)

cata g = g . recList (cata g) . outSortList
\end{code}

\clearpage

\subsection*{Problema 2}

% Primeira parte

Para a descoberta dos fatores primos de um número, não negativo,
foi implementado um anamorfismo de listas, |primes|, que, para um dado número,
devolve a sua lista única de fatores primos.

Este anamorfismo é definido por um gene que, para um número |n|, verifica se
este é menor que 2, caso em que devolve um valor à esquerda do tipo |1 + Int >< Int|
que indica o fim da iteração, ou, caso contrário, devolve um valor à direita do tipo
|1 + Int >< Int| cujo a primeira componente do par é o menor fator primo de |n|
e a segunda componente é o quociente da divisão de |n| pelo seu menor fator primo,
para que a iteração continue.

Para obtenção do menor fator primo de um número |n|, recorre-se a uma lista de inteiros
por compreensão, |x <- [2..n]|, que, para cada |x|, verifica se |n `mod` x == 0|, ou seja,
se |x| é um fator de |n|. Caso seja, |x| é o menor fator primo de |n| e
devolve-se o par |(x, n `div` x)|.

\includegraphics[width=.6\textwidth]{cp2425t_media/primes-ana.png}

\begin{code}
primes = anaList g
  where
    g n
      | n < 2     = i1 ()
      | otherwise = let p = head [x | x <- [2..n], n `mod` x == 0]
                    in i2 (p, n `div` p)
\end{code}

\clearpage

% Segunda parte

Para a geração da árvore de primos de um conjunto de inteiros, optou-se por uma
estratégia composta por dois passos principais:

\begin{enumerate}
    \item Geração de uma de árvore de expressões após a obtenção da lista de
        fatores primos para cada número do conjunto de entrada,
        recorrendo ao anamorfismo de \Exp |ana g| e a função |split primes id|, respetivamente.
    \item Construção da árvore de primos, com recurso à função |mergeTrees|, que
        recebe uma lista de árvores de expressões e as funde numa única árvore.
\end{enumerate}

\includegraphics[width=.6\textwidth]{cp2425t_media/prime_tree.png}

\begin{code}
prime_tree = mergeTrees . map (anaExp g . split primes id)
  where
    g ([], x) = i1 x
    g (x:xs, y) = i2 (x, [(xs, y)])

mergeTrees [tree] = tree
mergeTrees trees = Term 1 (mergeSubtrees trees)

mergeSubtrees [] = []
mergeSubtrees [tree] = [tree]
mergeSubtrees (Term o xs : Term o' ys : trees)
  | o == o'   = mergeSubtrees (Term o (xs ++ ys) : trees)
  | otherwise = Term o xs : mergeSubtrees (Term o' ys : trees)
mergeSubtrees (tree:trees) = tree : mergeSubtrees trees
\end{code}

\clearpage

\subsection*{Problema 3}

\includegraphics[width=.7\textwidth]{cp2425t_media/convolve-cata.png}

\begin{code}
convolve :: Num a => [a] -> [a] -> [a]
convolve = cataList conquer .: curry divide
  where
    (.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
    (.:) = (.) . (.)

    divide = uncurry zipper . cond (uncurry (>) . (length >< length)) swap id

    zipper n m = zip (replicate l n) (map (h m) [1..l])
      where
        l = length n + length m - 1

    h xs i = (++) r . reverse . take (i - l) $ drop l xs
      where
        l = max 0 (i - length xs)
        r = replicate l 0

    conquer = either g1 g2

    g1 = nil
    g2 = cons . (f >< id)
    f = sum . uncurry (zipWith (*))
\end{code}

\clearpage

\includegraphics[width=.8\textwidth]{cp2425t_media/convolve-hylo.png}

\vspace{1cm}

\hspace{3cm}
\includegraphics[width=.55\textwidth]{cp2425t_media/convolve-all-alt.png}

\vspace{0.5cm}

\begin{code}
convolve' = curry (uncurry drop . split sizeDiff (hyloList conquer divide . inFormat . swapper))
  where
    sizeDiff = abs . uncurry (-) . (length >< length)
    swapper  = cond (uncurry (>) . (length >< length)) id swap
    inFormat = split id (swap . split (flip (-) 1 . (2*) . length . p1) p2)

    conquer = either nil (cons . (applyMaths >< id))
      where applyMaths = sum . uncurry (zipWith (*)) . swap . p1

    divide = cond ((0 ==) . p2 . p2) (i1 . (!)) (i2 . dup . split (split (p1 . p1) makeList) ((id >< flip (-) 1) . p2))
      where
        makeList = buildPair . split p2 (length . p1 . p1)
        buildPair = uncurry drop . split (p2 . p1) (uncurry (++) . split (flip replicate 0 . p2) (reverse . p1 . p1))
\end{code}

\clearpage

\subsection*{Problema 4}

Definição do tipo:

Para o cálculo de |outExpr|, partiu-se do isomorfismo
de |outExpr| e |inExpr| e da definição de |inExpr|,
concluindo-se a seguinte definição de |outExpr|:

\begin{eqnarray*}
\start
|
	outExpr . inExpr = id
|
\just\equiv{ Def. inExpr }
|
    outExpr . [V, [N, uncurry T]] = id
|
\just\equiv{ 20: Fusão-|+| (2x) }
|
    [outExpr . V, [outExpr . N, outExpr . uncurry T]] = id
|
\just\equiv{ 17: Universal-|+| (2x), 1: Natural-id (2x) }
|
    lcbr3(
        outExpr . V = i1
    )(
        outExpr . N = i2 . i1
    )(
        outExpr . uncurry T = i2 . i2
    )
|
\just\equiv{ 72: Igualdade Extencional, 73: Def-comp, 86: Uncurry }
|
    lcbr3(
        outExpr (V v) = i1 v
    )(
        outExpr (N n) = (i2 . i1) n
    )(
        outExpr (T o exprs) = (i2 . i2) (o, exprs)
    )
|
\qed
\end{eqnarray*}

\begin{code}
outExpr (V v)       = i1 v
outExpr (N n)       = (i2 . i1) n
outExpr (T o exprs) = (i2 . i2) (o, exprs)
\end{code}

Para a definição de |recExpr|, recorreu-se ao functor base |baseExpr| assim como
tomou-se inspiração na definição de |recExp|, definida na biblioteca \Exp.
Deste modo, obteu-se que:

\begin{eqnarray*}
\start
|recExpr f = baseExpr id id f = id + (id + id >< map f)|
\end{eqnarray*}

\begin{code}
recExpr f = id -|- (id -|- id >< map f)
\end{code}

\noindent
\textit{Ana + cata + hylo}:

Através do isomorfismo entre |inExpr| e |outExpr|, as respetivas leis de isomorfismos,
´Shunt-left' (33) e ´Shunt-right' (34), assim como da lei de indução,
Universal-cata (46), da lei de coindução, Universal-ana (55),
e da definição de hilomorfismos, obteve-se as seguintes definições:

\begin{code}
cataExpr g   = g . recExpr (cataExpr g) . outExpr

anaExpr  g   = inExpr . recExpr (anaExpr g) . g

hyloExpr h g = cataExpr h . anaExpr g
\end{code}

\clearpage

\noindent
\emph{Maps}:

Para o tipo |Expr b| também foram desenvolvidas as instâncias de |Functor| e
|BiFunctor|, com as definições de |fmap| e |bmap| respetivamente, estas derivadas
da lei \textit{Def-map-cata} (51).

\begin{code}
instance Functor (Expr b) where
    fmap g = cataExpr (inExpr . baseExpr g id id)

instance BiFunctor Expr where
    bmap h g = cataExpr (inExpr . baseExpr g h id)
\end{code}

\noindent
\emph{Monad}:

\begin{code}
instance Monad (Expr b) where
    return  = V
    t >>= g = (muExpr . fmap g) t

muExpr :: Expr b (Expr b a) -> Expr b a
muExpr = cataExpr (either id (either N (uncurry T)))

instance Applicative (Expr b) where
    pure  = return
    (<*>) = aap
\end{code}

\noindent
\emph{Let expressions}:

Foram desenvolvidas duas versões da função |let_exp|, uma com recurso ao catamorfismo
|cataExpr| com um gene similar a |inExpr| com exceção do uso da função |f| para
as variáveis de |Expr|.

\begin{code}
let_exp f = cataExpr (either f (either N (uncurry T)))

let_exp' = muExpr .: fmap  -- equivalent to: let\_exp f = muExpr . fmap f
  where (.:) = (.) . (.)
\end{code}

A outra versão é equivalente à principal, como demonstrado seguidamente,
sendo esta uma versão \textit{pointfree}, que recorre às funções |muExpr| e |fmap|.

\begin{eqnarray*}
\start
|
    let_exp f = muExpr . fmap f
|
\just\equiv{ Def. muExpr, fmap f = T f }
|
    let_exp f = cata (either id (either N (uncurry T))) . T f
|
\just\equiv{ 52: Absorção-cata }
|
    let_exp f = cata (either id (either N (uncurry T)) . B(f, id))
|
\just\equiv{ |B(f, id) = baseExpr f id id = f + (id + id >< map id)| }
|
    let_exp f = cata (either id (either N (uncurry T)) . (f + (id + id >< map id)))
|
\just\equiv{ |map id = id|, 22: Absorção-|+|, 1: Natural-id, 15: Functor-id-|><| }
|
    let_exp f = cata (either f (either N (uncurry T)))
|
\qed
\end{eqnarray*}

\clearpage

\noindent
Catamorfismo monádico:

\textbf{TODO} Texto explicativo

\begin{code}
mcataExpr phi t = do { b <- traverseExpr (mcataExpr phi) (outExpr t); phi b }

traverseExpr f = either (return . i1) (either (return . i2 . i1) m)
  where m (op,es) = do { cs <- mapM f es; return $ i2 $ i2 (op, return cs) }
\end{code}

\noindent
Avaliação de expressões:

\textbf{TODO} Texto explicativo

\begin{code}
evaluate = mcataExpr eval
  where
  eval = either (const Nothing) (either Just evalTerm)
  evalTerm op = case op of
    (Add, Just [x,y]) -> Just (x + y)
    (Mul, Just [x,y]) -> Just (x * y)
    (Suc, Just [x]) -> Just (x + 1)
    (ITE, Just [x,y,z]) -> if x /= 0 then Just y else Just z
    _ -> Nothing
\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2425t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
