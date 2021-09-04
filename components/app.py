import os
import sys
import time
import math
import itertools
from token import INDENT

import sympy
from sympy.core import operations
from sympy.logic.boolalg import Not, And, Or, conjuncts, disjuncts

from components.graph import *


help_text = """

Користувач може використовувати одну з чотирьох опцій з відповідними параметрами (() означає, що аргумент не обов'язковий, [] відображають тип даних, що треба використовувати):
1) Сгенерувати граф з заданою кількістю вершин та направлених зв'язків та зберегти його у файл. Всі процесори системи в робочому стані.
----------------
generate_graph -vertexes [int] -input [int] -output [int] -total [int] -save [str + '.json']
-----------------
-vertexes: кількість вершин графу
-input: мінімальна кількість направлених зв'язків, що входять у вершину
-output: мінімальна кількість направлених зв'язків, що виходять з вершини
-total: сумарна кількість зв'язків. 
    Якщо буде менша або більше, ніж можливе за першими троьма параметрами, то буде автоматично перерахована
-save: назва файлу, в якому буде збережено граф

2) Сгенерувати стан процесорів у графі, що збережено у вказаному файлі, та зберегти граф у новому файлі з новими станами
----------------
generate_states -filename [str + '.json'] -mode [all | [int]] (-min_M [int] -max_M [int])
-----------------
-filename: назва файлу, з якого завантажити граф. 
    Новий граф буде збережено у файлі filename('.json' відкидається)+'_labled_[int].json'
-mode: спосіб генерації станів.
    Якщо обрати all, то буде створено всі можливі комбінаціі станів процесорів системи з M зламаних процесорів
-min_M, -max_m: мінімальная та максимально можлива кількість зламаних процесорів в системі відповідно. 
    Кількість обирається рандомно з заданого діапазону. 
    Якщо один із параметрів не задано, обидва параметри встановлюються за замовченням та дорівнюють максимальній М графу, що обраховується при його генерації

3) Провести тести та отримати формулу стану графу
----------------
make_tests -filename [str + '.json'] (-ok [0 < float < 1]) (-fail [0 < float < 1])
-----------------
-filename: назва файлу, з якого завантажити граф.
    Новий граф буде збережено у файлі filename('.json' відкидається)+'_formula.json'
-ok: ймовірність того, що результат тестування несправним процесором спарвного буде 0 (тестуємий процесор справний)
    За замовченням 0.5
-fail: ймовірність того, що результат тестування несправним процесором несправного буде 1 (тестуємий процесор несправний)
    За замовченням 0.5

4) Вивести поточну справку або у випадку, якщо команда не є у списку опції
----------------
help
-----------------
"""


def is_M_diagnosting(graph: Graph, M):
    K = 1
    while math.ceil(K/2) <= M:
        # print(K)
        combinations = list(itertools.combinations(graph.vertexes.keys(), K))
        for F in combinations:
            F_inputs = []
            for item in F:
                F_inputs = F_inputs + list(graph.vertexes[item].input_links)
            F_inputs = [elem for elem in F_inputs if elem not in F]
            T = len(F_inputs)
            if T <= M - math.ceil(K/2):
                return 'No'
        K += 1
    return 'Yes'


def get_max_M(graph: Graph):
    M = len(graph.vertexes)
    K = 1
    while math.ceil(K/2) <= M:
        combinations = list(itertools.combinations(graph.vertexes.keys(), K))
        time_start = time.time()
        for F in combinations:
            print(len(combinations))
            print(len(F))
            F_outputs = []
            for item in F:
                F_outputs.extend([elem for elem in list(graph.vertexes[item].output_links) if elem not in F])
            T = len(F_outputs)
            tM = T + math.ceil(K/2) - 1
            M = tM if tM < M else M
        K = K + 1
        print('2', time.time() - time_start)
    return M


def make_new_disjuncts_of_conjuncts(disjuncts_of_conjuncts, add_disjuncts_of_conjuncts):
    if not disjuncts_of_conjuncts:
        return add_disjuncts_of_conjuncts

    new_formula = Or()
    for item1 in disjuncts_of_conjuncts:
        for item2 in add_disjuncts_of_conjuncts:
            new_formula = Or(new_formula, And(item1, item2))
    return list(disjuncts(new_formula))


def remove_more_than_M_inversions(disjuncts_of_conjuncts, vertexes_symbols_list, M):
    # Удаляем те конституенты, где больше, чем М инверсий
    result = []
    for item in disjuncts_of_conjuncts:
        counter_inversies = 0
        for elem in conjuncts(item):
            if Not(elem) in vertexes_symbols_list:
                counter_inversies += 1
        if counter_inversies <= M:
            result.append(item)
            # disjuncts_of_conjuncts.remove(item)
    return result


def remove_A_notA(disjuncts_of_conjuncts):
    disjuncts_of_conjuncts = disjuncts_of_conjuncts.copy()
    for item in tuple(disjuncts_of_conjuncts):
        # print(item)
        for elem1 in conjuncts(item):
            if elem1 in [Not(elem2) for elem2 in conjuncts(item)]:
                disjuncts_of_conjuncts.remove(item)
                break
    return disjuncts_of_conjuncts



def make_absorptions(disjuncts_of_conjuncts):
    disjuncts_of_conjuncts = disjuncts_of_conjuncts.copy()
    for item1 in tuple(disjuncts_of_conjuncts):
        for item2 in tuple(disjuncts_of_conjuncts):
            if item1 != item2 and set(conjuncts(item1)).issubset(set(conjuncts(item2))):
                disjuncts_of_conjuncts.remove(item2)
    return disjuncts_of_conjuncts


def get_formula(graph: Graph, M, prob_ok, prob_fail):
    vertexes_symbols = {vertex_key: sympy.symbols(f'x{vertex_key}') for vertex_key in graph.vertexes.keys()}
    vertexes_symbols_list = [vertexes_symbols[vertex_key] for vertex_key in vertexes_symbols.keys()]
    disjuncts_of_conjuncts = []

    tests_counter = 0
    
    print(f"Links quantity: {len(tuple(graph.links))}")
    while len(disjuncts_of_conjuncts) > 1 or len(disjuncts_of_conjuncts) == 0:
        tests_counter += 1
        links_counter = 0
        print(f"Test {tests_counter}")

        for link in tuple(graph.links):
            links_counter += 1
            # print(links_counter)
            testerer = vertexes_symbols[link[0]]
            tested = vertexes_symbols[link[1]]
            test_result = graph.test_vertex(link[0], link[1], prob_ok, prob_fail)

            if test_result == 'ok':
                disjuncts_of_conjuncts = make_new_disjuncts_of_conjuncts(disjuncts_of_conjuncts, [Not(testerer), tested])
            else:
                disjuncts_of_conjuncts = make_new_disjuncts_of_conjuncts(disjuncts_of_conjuncts, [Not(testerer), Not(tested)])
            disjuncts_of_conjuncts = remove_more_than_M_inversions(disjuncts_of_conjuncts, vertexes_symbols_list, M)
            disjuncts_of_conjuncts = remove_A_notA(disjuncts_of_conjuncts)
            disjuncts_of_conjuncts = make_absorptions(disjuncts_of_conjuncts)
        disjuncts_of_conjuncts = remove_A_notA(disjuncts_of_conjuncts)
        
        print(disjuncts_of_conjuncts)
        disjuncts_of_conjuncts = make_absorptions(disjuncts_of_conjuncts)

        formula = sympy.logic.simplify_logic(Or(*disjuncts_of_conjuncts))

        if len(disjuncts(formula)) == 1:
            return [elem for elem in conjuncts(formula)]        
    return disjuncts_of_conjuncts

            
# def tests():
#     graph_parameters = Graph_parameters(
#         vertexes_quanitity = 30,
#         minimal_input_links_quantity = 3,
#         minimal_output_links_quantity = 3,
#         total_links_quantity = 6)

#     graph = Graph()

#     graph.load('test7.json')
#     graph.generate_graph(graph_parameters)
#     max_m = graph.max_m
#     print(f"Max M: {max_m}")
#     # M = graph_parameters.M
#     M = max_m
#     graph.generate_states(M, M, [i for i in range(M)])
#     graph.save('test7.json')
#     print('states_generated')

#     is_M_diagnosting_result = is_M_diagnosting(graph, M)
    
#     print(is_M_diagnosting_result)
#     print('------------')
#     if is_M_diagnosting_result == 'Yes':
#         formula = get_formula(graph, M)
#         print(f"Formula = {formula}")

#         pretty_formula = sympy.logic.simplify_logic(And(*formula))
#         print(pretty_formula)


def run_app():

    graph = Graph()

    input_argv = sys.argv[1:]
    try:
        option = input_argv[0]
    except IndexError:
        option == 'not'

    if option == 'generate_graph':
        graph_parameters = Graph_parameters(
            vertexes_quanitity = int(input_argv[input_argv.index('-vertexes') + 1]),
            minimal_input_links_quantity = int(input_argv[input_argv.index('-input') + 1]),
            minimal_output_links_quantity = int(input_argv[input_argv.index('-output') + 1]),
            total_links_quantity = int(input_argv[input_argv.index('-total') + 1]))
        graph.generate_graph(graph_parameters)
        graph.save(input_argv[input_argv.index('-save') + 1])

    elif option == 'generate_states':
        filename = input_argv[input_argv.index('-filename') + 1]
        graph.load(filename)
        filename = filename.replace('.json', '')
        try:
            min_fail = input_argv[input_argv.index('-min_M') + 1]
            max_fail = input_argv[input_argv.index('-max_M') + 1]
        except ValueError:
            min_fail = graph.max_m
            max_fail = graph.max_m
        mode = input_argv[input_argv.index('-mode') + 1]

        if mode.isdigit():
            for i in range(int(mode)):
                graph.generate_states(min_fail, max_fail)
                graph.save(f'{filename}_labled_{i}.json')
        elif mode == 'all':
            combinations = list(itertools.combinations(list(graph.vertexes.keys()), graph.max_m))
            for selected_vertexes in combinations:
                graph.generate_states(min_fail, max_fail, list(selected_vertexes))
                graph.save(f'{filename}_labled_{combinations.index(selected_vertexes)}.json')
        else:
            raise ValueError('Mode have to be digit or "all"')
        # graph.generate_states(min_fail, max_fail, )

    elif option == 'make_tests':
        filename = input_argv[input_argv.index('-filename') + 1]
        graph.load(filename)
        filename = filename.replace('.json', '')
        try:
            prob_ok = input_argv[input_argv.index('-ok') + 1]
        except ValueError:
            prob_ok = 0.5
        try:
            prob_fail = input_argv[input_argv.index('-fail') + 1]
        except ValueError:
            prob_fail = 0.5
        M = graph.max_m
        is_M_diagnosting_result = is_M_diagnosting(graph, M)
        if is_M_diagnosting_result == 'Yes':
            formula = get_formula(graph, M, float(prob_ok), float(prob_fail))
            print(f"Formula list = {formula}")

            pretty_formula = sympy.logic.simplify_logic(And(*formula))
            print(f"Formula = {pretty_formula}")
            with open(os.path.join(f'{filename}_formula.json'), 'w+') as json_file:
                json.dump({'formula': str(pretty_formula), 'formula_list': [str(item) for item in formula]}, json_file)
        else:
            print(f'{filename} is not M-diagnosted')

    elif option == 'help':
        print(help_text)
    
    else:
        print('Use one of options: "generate_graph", "generate_states", "make_tests" or "help"')


# def main():
#     # tests()
    # run_app()


# if __name__ == '__main__':
#     run_app()