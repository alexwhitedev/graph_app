import random
import json
import os
import math
import time
import itertools


class Graph_parameters():
    def __init__(self, vertexes_quanitity, minimal_input_links_quantity, minimal_output_links_quantity, total_links_quantity) -> None:
        self.vertexes_quanitity = vertexes_quanitity
        self.min_input_links_quantity = self.set_links(minimal_input_links_quantity, 'input')
        self.min_output_links_quantity =self.set_links(minimal_output_links_quantity, 'output')
        self.total_links_quantity = self.set_total_links(total_links_quantity)

    def set_total_links(self, total_links_quantity):
        min_total_links = self.vertexes_quanitity * self.min_input_links_quantity if self.min_input_links_quantity > self.min_output_links_quantity else self.min_output_links_quantity * self.vertexes_quanitity
        if total_links_quantity < min_total_links:
            print(f'Setted total links ({total_links_quantity}) less than min total links quantity ({min_total_links}). So {min_total_links} setted')
            return min_total_links
        max_total_links = self.vertexes_quanitity * (self.vertexes_quanitity - 1)
        if total_links_quantity > max_total_links:
            print(f'Setted total links ({total_links_quantity}) more than max total links quantity ({max_total_links}). So {max_total_links} setted')
            return max_total_links
        return total_links_quantity 

    def set_links(self, quantity, opt):
        if quantity >= self.vertexes_quanitity:
            print(f'Min {opt} quantity = {quantity} > (vertex_quantity - 1) = {self.vertexes_quanitity - 1}. So {self.vertexes_quanitity - 1} was setted')
            return self.vertexes_quanitity - 1
        return quantity


class Vertex():
    def __init__(self, id : int, state: str):
        self.__id : int = id
        self.__state : bool = self.set_state(state)
        self.__input_links : set = set()
        self.__output_links : set = set()

    def create_output_link(self, input_vertex_id):
        self.__output_links.add(input_vertex_id)

    def create_input_link(self, output_vertex_id):
        self.__input_links.add(output_vertex_id)

    def set_state(self, state: str):
        if state not in ['ok', 'broken']:
            raise ValueError
        self.__state = state
        return state

    @property
    def output_links(self):
        return self.__output_links

    @property
    def input_links(self):
        return self.__input_links

    @property
    def id(self):
        return self.__id
        
    @property
    def state(self):
        return self.__state


class Graph_bounds():
    def __init__(self):
        self.__vertexes : dict = dict()
        self.__links : set = set()
        self.__max_m: int = 0

    def clear_graph(self):
        self.__vertexes = dict()
        self.__links = set()

    def add_vertex(self, id : int = None, state : str = 'ok'):
        if id == None:
            id = len(self.__vertexes)
            while id in self.__vertexes.keys():
            # Для защиты от накладывания сгенерированного идентификатора на существующий при неупорядоченном наборе идентификаторов
                id += 1
        if type(id) != int or id < 0 or id in self.__vertexes.keys():
            raise ValueError(f'Vertex id should be unique int > 0; but {id} given; ids {[i for i in self.__vertexes.keys()]} exists')
        self.__vertexes[id] = Vertex(id, state)

    def add_link(self, output_vertex_id : int, input_vertex_id : int):
        if output_vertex_id not in self.__vertexes.keys():
            raise KeyError(f'No output_vertex_id = {output_vertex_id} in Graph.__vertexes. Vertexes: {self.__vertexes.keys()}')
        if input_vertex_id not in self.__vertexes.keys():
            raise KeyError(f'No input_vertex_id = {output_vertex_id} in Graph.__vertexes. Vertexes: {self.__vertexes.keys()}')

        new_link = (output_vertex_id, input_vertex_id)
        if new_link not in self.__links:
            self.__links.add(new_link)
            self.__vertexes[output_vertex_id].create_output_link(input_vertex_id)
            self.__vertexes[input_vertex_id].create_input_link(output_vertex_id)

    def test_vertex(self, tester_vertex_id : int, tested_vertex_id : int, possibility_ok: float = 0.5, possibility_broken: float = 0.5):
        if (tester_vertex_id, tested_vertex_id) not in self.__links:
        #  Check if vertexes and links in graph
            raise ValueError(f'({tester_vertex_id}, {tested_vertex_id}) not in Graph.__links')
        if 0 < (possibility_ok) > 1 or 0 > (possibility_broken) > 1:
            raise ValueError(f'Possibility x must be 0 < x < 1, but {possibility_ok}, {possibility_broken} passed')
        tester = self.__vertexes[tester_vertex_id]
        tested = self.__vertexes[tested_vertex_id]
        
        if tester.state == 'broken':
            if tested.state == 'ok':
                if random.random() <= possibility_ok:
                    return 'ok'
                else:
                    return'broken'
            else:
                if random.random() <= (1 - possibility_broken):
                    return 'ok'
                else:
                    return'broken'
        elif tester.state == 'ok':
            if tested.state == 'broken':
                return 'broken'
            return 'ok'

    def set_max_m(self, max_m):
        self.__max_m = max_m

    @property
    def links(self):
        return self.__links

    @property
    def vertexes(self):
        return self.__vertexes

    @property
    def max_m(self):
        return self.__max_m


class Graph(Graph_bounds):

    def __init__(self):
        super().__init__()

    
    def get_max_m(self):
        M = len(self.vertexes)
        K = 1
        while math.ceil(K/2) <= M:
            combinations = list(itertools.combinations(self.vertexes.keys(), K))
            for F in combinations:
                F_outputs = []
                for item in F:
                    F_outputs.extend([elem for elem in list(self.vertexes[item].output_links) if elem not in F])
                T = len(F_outputs)
                tM = T + math.ceil(K/2) - 1
                M = tM if tM < M else M
            K = K + 1
        return M


    def generate_graph(self, graph_parameters: Graph_parameters):
        self.clear_graph()
        for i in range(graph_parameters.vertexes_quanitity):
            self.add_vertex()

        #  Создать минимум исходящих связей 
        for vertex_key in self.vertexes.keys():
            vertex = self.vertexes[vertex_key]
            for i in range(graph_parameters.min_output_links_quantity - len(vertex.output_links)):
                input_vertex = random.choice(
                    [key for key in self.vertexes.keys() if key not in list(vertex.output_links) + [vertex.id]])
                self.add_link(vertex.id, input_vertex)

        #  Создать минимум входящих связей
        for vertex_key in self.vertexes.keys():
            vertex = self.vertexes[vertex_key]
            if len(vertex.input_links) < graph_parameters.min_input_links_quantity:
                for i in range(graph_parameters.min_input_links_quantity - len(vertex.input_links)):
                    output_vertex = random.choice(
                        [key for key in self.vertexes.keys() if key not in list(vertex.input_links) + [vertex.id]])
                    self.add_link(output_vertex, vertex.id)

        #  Добавить связи до общего количества связей
        while len(self.links) < graph_parameters.total_links_quantity:
            open_for_input = [vertex_key for vertex_key in self.vertexes.keys() if len(self.vertexes[vertex_key].input_links) < (graph_parameters.vertexes_quanitity - 1)]
            open_for_output = [vertex_key for vertex_key in self.vertexes.keys() if len(self.vertexes[vertex_key].output_links) < (graph_parameters.vertexes_quanitity - 1)]
            vertex_input = random.choice(open_for_input)
            vertex_output = random.choice(open_for_output)
            
            self.add_link(vertex_output, vertex_input)

        self.set_max_m(self.get_max_m())

        print(f'Graph has been generated:\n\tVertexes_quantity = {len(self.vertexes)}\n\tLinks_quantity = {len(self.links)}')


    def save(self, filename):
        if filename[-5:] != '.json':
            raise ValueError('Filename must be .json format')
        output_dict = {
            'quantities': {
                'vertexes': len(self.vertexes),
                'links': len(self.links)
            },
            'max_m': self.max_m,
            'vertexes': [
                {
                    'id': self.vertexes[vertex_key].id,
                    'state': self.vertexes[vertex_key].state,
                    'input_links': tuple(self.vertexes[vertex_key].input_links),
                    'output_links': tuple(self.vertexes[vertex_key].output_links),
                } for vertex_key in self.vertexes.keys()],
            'links': [{
                'output': link[0],
                'input': link[1],
            } for link in self.links],
        }
        with open(os.path.join(f'{filename}'), 'w+') as json_file:
            json.dump(output_dict, json_file)


    def load(self, filename):
        #  С целью защиты от "дурака" и изменений в JSON файле, связи устанавливаются по объекту "links" с нуля.
        #  В связи с этим, конечное количество линков между вершинами может не совпадать с линками внутри объектов. Однако это гарантирует целосный граф
        #  TODO Сделать проверку на соответсвие графа в файле и конечного графа
        if filename[-5:] != '.json':
            raise ValueError('Filename must be .json format')
        self.clear_graph()
        with open(os.path.join(f'{filename}'), 'r+') as json_file:
            load_dict = json.load(json_file)
        for new_vertex in load_dict['vertexes']:
            self.add_vertex(new_vertex['id'], new_vertex['state'])
        for new_links in load_dict['links']:
            self.add_link(new_links['output'], new_links['input'])
        self.set_max_m(load_dict['max_m'])

    def generate_states(self, broken_quantity, selected_vertexes : list =[]):
        #  Устанавливаем везде состояние ОК, если загружали с файла и уже есть какие-то состояния
        for vertex_key in self.vertexes.keys():
            self.vertexes[vertex_key].set_state('ok')
        # broken_quantity = random.randint(min_broken_quantity, max_broken_quantity)
        self.set_max_m(broken_quantity)

        #  RANDOM
        if not selected_vertexes:
            selected_vertexes = []
            vertexes = list(self.vertexes.keys())
            for i in range(broken_quantity):
                vertex_key = random.choice(vertexes)
                selected_vertexes.append(vertex_key)
                vertexes.remove(vertex_key)
                vertex = self.vertexes[vertex_key]
                vertex.set_state('broken')
            print(selected_vertexes)
        #  SELECTED VERTEXES
        else:
            print(selected_vertexes)
            for i in range(broken_quantity):
                self.vertexes[selected_vertexes[0]].set_state('broken')
                selected_vertexes.pop(0)



