""" Algoritmo genético para la resolución de 3-SAT.
El input es una instancia de 3-SAT, es decir, una fórmula F(X_1,...X_n) del cálculo proposicional en forma normal
conjuntiva de 3-cláusulas leída de un fichero en formato cnf. El algoritmo busca una interpretación de la fórmula que la
satisfaga.

Los cromosomas son las posibles interpretaciones (x_1,...x_n) en {0,1}^n. El fitness de un cromosoma es número de
cláusulas satisfechas por la interpretación definida como el propio cromosoma. La selección de padres se hace mediante
ruleta proporcional al fitness de la población. La nueva población se forma mediante una selección elitista de los dos
mejores individuos según su fitness. El resto de individuos se obtiene mediante cruce uniforme de los cromosomas de los
padres y una mutación con probabilidad 0.9 que invierte cada gen con probabilidad 0.5.

Además, aplicamos una estategia de búsqueda local que dada una interpretación, encuentra otra interpretación con el
mayor fitness tal que no mejora invirtiendo ninguna variable.

Nos basamos en el artículo:
E. Marchiori, C. Rossi, "A Flipping Genetic Algorithm for Solving Hard 3-SAT Problems", 2000.
"""

from sympy import *
from random import random, shuffle, choices
from re import match
from datetime import *


# Función que lee una fórmula bien formada del cálculo proposicional en forma normal
# conjuntiva de 3-cláusulas y la guarda como una fórmula del paquete sympy.
def lee_cnf(nom_archivo):
    fichero = open(nom_archivo, "r")  # Abrimos el fichero.
    linea = ""
    while not match("p", linea):  # Buscamos la línea de parámetros.
        linea = fichero.readline()
    linea = linea.split()  # La línea de parámetros.
    n_var = int(linea[2])  # Número de variables.
    n_cla = int(linea[3])  # Número de cláusulas.
    lineas = []
    linea = fichero.readline()  # Primera cláusula.
    while not match("%", linea):  # Guardamos cada línea hasta %.
        lineas.append(linea.split())
        linea = fichero.readline()
    fichero.close()  # Cerramos el fichero.
    lineas = [[int(_) for _ in lin][:-1] for lin in lineas]  # Quitamos los ceros.
    var("x1:" + str(n_var))  # Generamos las variables simbólicas.
    form = [[0] * 3 for _ in range(n_cla)]  # Inicializamos las cláusulas.
    for i in range(len(lineas)):  # Cambiamos de números a variables.
        for j in range(3):
            if lineas[i][j] > 0:
                form[i][j] = symbols("x" + str(lineas[i][j]))
            else:
                form[i][j] = ~symbols("x" + str(abs(lineas[i][j])))
    form = [_[0] | _[1] | _[2] for _ in form]  # Disyunciones
    FORM = And(*form)  # Fórmula en forma normal conjuntiva de 3-cláusulas.
    return FORM

# Leemos la fórmula booleana del archivo cnf.

# Fórmula booleana sencilla para probar los métodos.
# F = lee_cnf("easywff.cnf")

# Familia de fómulas booleanas satisfactibles generadas uniformemente con ratio 4.36.
# 20 variables y 91 cláusulas
F = lee_cnf("uf20-01.cnf")
# F = lee_cnf("uf20-02.cnf")
# F = lee_cnf("uf20-03.cnf")
# F = lee_cnf("uf20-04.cnf")
# El algoritmo encuentra una interpretación que la satisface en unos 7 segundos utilizando solo
# la búsqueda local.

# 50 variables y 218 cláusulas
# F = lee_cnf("uf50-01.cnf")
# F = lee_cnf("uf50-02.cnf")
# F = lee_cnf("uf50-03.cnf")
# F = lee_cnf("uf50-04.cnf")

# 75 variables y 325 cláusulas
# F = lee_cnf("uf75-01.cnf")
# F = lee_cnf("uf75-01.cnf")
# F = lee_cnf("uf75-01.cnf")
# F = lee_cnf("uf75-01.cnf")

# 100 variables y 430 cláusulas
# F = lee_cnf("uf100-01.cnf")
# F = lee_cnf("uf100-02.cnf")
# F = lee_cnf("uf100-03.cnf")
# F = lee_cnf("uf100-04.cnf")

# Familia AIM de fórmulas booleanas satisfactibles con solución única.
# 50 variables y 80 cláusulas
# F = lee_cnf("aim-50-1_6-yes1-1.cnf")
# F = lee_cnf("aim-50-1_6-yes1-2.cnf")

print("Fórmula booleana:\n", F)


def variables(f=F):  # Devuelve las variables de la fórmula.
    return var("x1:" + str(len(f.atoms()) + 1))


def fitness(inter, f=F):  # Número de cláusulas satisfechas por la interpretación.
    xi = variables(f)
    if not inter:  # Si es la interpretación vacía, es 0.
        return 0
    fit = 0
    for _ in f.args:  # Recorremos las cláusulas
        if _.subs(zip(xi, inter)):  # Si se satisface,
            fit += 1  # sumamos 1.
    return fit


def ganancia(inter, pos, f=F):  # Diferencia de fitness antes y después de cambiar la posición en la interpretación.
    xi = variables(f)
    clausulas = []
    for _ in F.args:  # Recorremos las cláusulas de la fórmula y guardamos las que contengan la variable.
        if xi[pos] in _.atoms():
            clausulas.append(_)
    inter2 = inter.copy()
    inter2[pos] ^= True  # Consideramos la interpretación con el opuesto para la variable.
    fit0, fit1 = 0, 0
    for _ in clausulas:  # Recorremos las cláusulas con la variable y calculamos la diferencia de fitness.
        if _.subs(zip(xi, inter)):
            fit0 += 1
        if _.subs(zip(xi, inter2)):
            fit1 += 1
    return fit1 - fit0, inter2


def flip_heuristic(inter, f=F):  # Búsqueda local que maximiza el fitness por intercambio de variables.
    list_var = list(f.atoms())
    n_var = len(list_var)
    index_var = list(range(n_var))
    shuffle(index_var)  # Mezclamos los índices de las variables en orden aleatorio.
    mejora = 1
    interr = inter.copy()
    while mejora > 0:  # Mientras sigamos mejorando
        mejora = 0
        for i in range(n_var - 1):  # Para cada variable en orden aleatorio.
            gain, inter2 = ganancia(interr, index_var[i], f)  # calculamos la ganancia al invertirla.
            if gain >= 0:  # Si la ganancia es positiva,
                interr = inter2  # aceptamos la inversión
                mejora += gain  # Hemos mejorado el fitness de la interpretación.
    return interr


def satisface(pob, f=F):  # Comprueba si algún individuo de la población satisface la fórmula.
    xi = variables(f)
    for _ in pob:  # Recorremos la población.
        if F.subs(zip(xi, _)):  # Evaluamos la fórmula y, si se satisface, retornamos True y la interpretación.
            return True, _
    return False, None


def elitista2(pob):  # Toma una población y devuelve los dos individuos con mayor fitness para la selección elitista.
    pob2 = pob.copy()
    pob2.sort(key=fitness)  # Ordenamos la población de manera creciente según el fitness.
    return pob2[-1], pob2[-2]


def selec_padres(pob):  # Escoge dos padres con probabilidad proporcional al fitness.
    fit = [fitness(_) for _ in pob]
    total = sum(fit)
    prob = [_ / total for _ in fit]  # Lista de probabilidades proporcional al fitness.
    return choices(pob, prob, k=2)


def cruce_uniforme(padre1, padre2):  # Devolvemos un hijo fruto de un cruce uniforme de los padres.
    mascara = [choices([True, False], k=len(padre1))]  # Generamos uniformemente una máscara de cruce.
    hijo = [False] * len(padre1)  # Inicializamos un hijo de ceros.
    for _ in range(len(mascara)):  # Recorremos la máscara.
        if mascara[_]:  # Si el elemento es 1,
            hijo[_] = padre1[_]  # el gen del hijo es el del padre1.
        else:  # Si el elemento es 0,
            hijo[_] = padre2[_]  # el gen del hijo es el del padre2.
    return hijo


def mutacion(inter, pmut1, pmut2):  # Mutación del cromosoma inter.
    hijo = inter
    if random() <= pmut1:  # Decidimos si mutamos al hijo.
        for _ in range(len(hijo)):  # Recorremos los genes del hijo.
            if random() <= pmut2:  # Decidimos si mutamos el gen.
                hijo[_] ^= True  # Invertimos el valor del gen en la interpretación.
    return hijo


def genetic_sat(f=F, n_ind=10, tmax=300000, pmut1=0.9, pmut2=0.5, busqueda=True):
    n_var = len(F.atoms())
    P = [choices([True, False], k=n_var) for _ in range(n_ind)]  # Generamos la población inicial.
    if busqueda:
        P = [flip_heuristic(_) for _ in P]  # Aplicamos la búsqueda local a cada individuo de la población.
    t = 0
    while t < tmax and not satisface(P, f)[0]:  # Si no hemos llegado al número máximo de generaciones y la población no
        # satisface la fórmula.
        t += 1
        print("Generación: ", t)
        P0 = P  # Reasignamos la población actual.
        P = []
        P.extend(elitista2(P0))  # Adición elitista de los dos mejores individuos de la población anterior.
        while len(P) < len(P0):
            padre1, padre2 = selec_padres(P0)  # Selección por ruleta de los padres.
            hijo = cruce_uniforme(padre1, padre2)  # Cruce uniforme de los padres.
            hijo = mutacion(hijo, pmut1, pmut2)  # Mutación del hijo.
            if busqueda:
                hijo = flip_heuristic(hijo, f)
            P.append(hijo)  # Añadimos el hijo a la población.
            print("Hijo", len(P))
            if satisface([hijo], f)[0]:
                print("La fórmula booleana introducida es satisfecha por la interpretación:\n", hijo)
                return True, hijo, t
    sat = satisface(P, f)
    if sat[0]:
        print("La fórmula booleana introducida es satisfecha por la interpretación:\n", sat[1])
        return True, sat[1], t
    else:
        print("Se ha alcanzado el número máximo de generaciones.")
        return False, elitista2(P)[-1]


tiempo0 = datetime.now()
genetic_sat(F)  # Ejecutamos el algoritmo genético con búsqueda local.
tiempo1 = datetime.now()
print("Tiempo de cálculo: ", tiempo1 - tiempo0)  # Tiempo de cálculo
