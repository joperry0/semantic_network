# File: knowclass.py
# Author: Jo Perry
# This is a basic semantic network that reads a text file
# containing basic relations and then questions to ask about
# what relations exist.

# Input Requirements:
#
# To assert a fact:
# (fact (is-a node type))
# (fact (connected node1 node2))
#
# To raise a query:
# (query (is-a node type))
# (query (connected node1 node2))
# (query  value (is-a node value))
# (query value (connected node value))
# (query value (connected value node))
# (query value (and …))

# Example Input file:
#
# (fact (is-a seat1 seat))
# (fact (is-a l1 leg))
# (fact (is-a l2 leg))
# (fact (is-a l3 leg))
# (fact (connected  l1 seat1))
# (fact (connected  l2 seat1))
# (fact (connected l3 seat1))
# (query (connected  l1 l2))
# (query (connected  l1 seat1))
# (query value (is-a value seat))
# (query value (and (is-a  value leg) (connected value  l1 (connected value seat2)))
# (query value (and (is-a value leg) (connected value seat1)))

# Example Output:
#
# No
# Yes
# seat1
# None
# l1

#!/usr/bin/env python

from optparse import OptionParser
import os, logging, re, math, operator
from types import *
import pyparsing

thecontent = pyparsing.Word(pyparsing.srange("[a-zA-Z0-9_\-]"))
parens = pyparsing.nestedExpr( '(', ')', content=thecontent)

posit = re.compile(r'(?i)fact')
ask = re.compile(r'(?i)query')
retrieve = re.compile(r'(?i)value')
operats = re.compile(r'(?i)(and|or)')

identity = set(['is-a'])
unknown = set(['value'])
relations = set(['connected'])
negative = set(['No'])
empty = set(['None'])

attributes = ['name','connected', 'weight']
val_defaults = ['', set(), 0]

# Create an arbitrary class
#  class NAME(BaseClass):
#   self.kwarg1 = kval1
#   self.kwarg2 = kval2
#   self.kwarg3 = kval3
#   ...
#   self.kwargN = kvalN

# author: jsbueno, http://stackoverflow.com/users/108205/jsbueno
# source: http://stackoverflow.com/a/15247892

class BaseClass(object):
    def __init__(self, classtype):
        self._type = classtype
    def __getitem__(self, attrib):
    	return attrib

def ClassFactory(name, argnames, BaseClass=BaseClass):
    def __init__(self, **kwargs):
        for key, value in kwargs.items():
            if key not in argnames:
                raise TypeError("Argument %s not valid for %s" 
                    % (key, self.__class__.__name__))
            setattr(self, key, value)
        BaseClass.__init__(self, name[:-len("Class")])
    newclass = type(name, (BaseClass,),{"__init__": __init__})
    return newclass

class Knowledge:
	def __init__(self, collection_path, spread, alpha):
		self.spread = spread
		self.alpha = alpha
		self.files = []

		self.facts = {}
		self.queries = []
		self.results = []

		self.classes = {}
		self.types = {}
		self.entities = {}

		# Read in and process all .txt files in folder given by collection_path
		for f in os.listdir(collection_path):
			if re.search(r'txt$', f) is not None:
				f_path = os.path.join(collection_path, f)

				if self.read_in(f_path) is False:
					print("Read in failed on %s." % f_path)
					return False
				self.files.append(f in enumerate(os.listdir(collection_path)))

		# Format results and print out
		for res_id, result in enumerate(self.results):
			# Get the object entity out of set of relevant retrieved entities with highest activated semantic weight if set not empty
			if type(result).__name__ == 'set' and result != set():
				# result = sorted((self.entities[x] for x in list(result)), key=lambda y: getattr(y, 'weight'), reverse=True)[0].name
				result = sorted((self.entities[x] for x in list(result)), key=lambda y: getattr(y, 'weight'), reverse=True)

			# Set result to None if set is empty
			elif result == set():
				result = 'None'

			print("%d of %d: %s" % (res_id+1, len(self.results), result)) #, self.queries[res_id])

	# Read in a text file given by f_path and process any facts / queries contained within
	def read_in(self, f_path):
		self.f_ptr = open(f_path)

		# Keep memory for object text read_in to most current file's text
		self.text = []

		# Convert multi-spacing to single-spacing, downcase text, and split into lines
		text = re.sub(r'\n{2,}', '\n', self.f_ptr.read(), re.MULTILINE)
		text = re.sub(r'\s{3,}', ' ', text)
		text = re.sub(r' \n', ' ', text).lower()
		lines = text.split("\n")

		for line in lines:
			line = re.sub(r'\s{2,}',' ',line)
			# Ignore lines without fact or query following an opening (
			if re.search(r'(?i)\((fact|query)', line) is not None:
				ary = parens.parseString(line)

				for item in ary:
					# Assertion of FACT : Output ( None )
					if posit.search(str(item)) is not None:
						self.process_fact(item[1])

					# Request for DOCUMENTS : Output ( Set )
					elif retrieve.search(str(item)) is not None:
						self.queries.append(item[2])
						self.results.append(self.retrieve_query(item[2]))

					# Boolean query for ENTITY RELATION : Output ( Yes / No )
					elif ask.search(str(item)) is not None:
						self.queries.append(item[1])
						self.results.append(self.process_query(item[1]))

		self.f_ptr.close
		self.f_ptr = None

		return True

	def process_fact(self, fact):
		relation, ent1, ent2 = fact

		# IS-A -> creates an object of type ent2, with ent1 in name field
		if relation in identity: 
			# spawn an entity of type ent2 with attributes given in global
			if not ent2 in self.classes:
				self.classes[ent2] = ClassFactory(ent2, attributes)
			if not ent1 in self.entities:
				val_defaults[0] = ent1
				val_defaults[1] = set()

				self.entities[ent1] = self.classes[ent2]()
				for idx, attrib in enumerate(attributes):
					setattr(self.entities[ent1], attrib, val_defaults[idx])

			# add ent1 to a set for quick lookup
			if not ent2 in self.types:
				self.types[ent2] = set([ent1])
			else:
				self.types[ent2].add(ent1)

		# All other binary relations between entities - mutually linking ( A->B and B->A )
		if relation in relations:
			if ent1 in self.entities and ent2 in self.entities:
				if not ent1 in getattr(self.entities[ent2], relation):
					getattr(self.entities[ent2], relation).add(ent1)

				if not ent2 in getattr(self.entities[ent1], relation):
					getattr(self.entities[ent1], relation).add(ent2)

	# Recursively retrieves all relevant documents to a given query
	def retrieve_query(self, query):
		result = set()
		flag = 0
		# Nested query logic
		if operats.search(str(query)) is not None:
			for qu in query[1:]: # logic here does not work entirely correctly
				if type(qu).__name__ == 'ParseResults':
					if query[0] == 'and': 
						if flag == 0:
							result = self.retrieve_query(qu)
							flag = 1
						else:
							result &= self.retrieve_query(qu)

					elif query[0] == 'or':
						if flag == 0:
							result = self.retrieve_query(qu)
							flag = 1
						else:
							result |= self.retrieve_query(qu)
		else: # Single-level query logic
			relation, _, ent2 = query
			# add every instance of object type ent2 to result and apply semantic spread
			if relation in identity:
				if ent2 in self.classes:
					for ent1 in self.types[ent2]:
						self.apply_spread(ent1)
						result.add(ent1)
				else: # invalid entity type, clear result set
					result.clear()

			# add every entity w/relation to object ent2 to result and apply semantic activation spread
			if relation in relations:
				if ent2 in self.entities:
					for ent1 in getattr(self.entities[ent2], relation):
						self.apply_spread(ent1)
						result.add(ent1)
				else: # invalid entity, clear result set
					result.clear()

		return result

	# Query the database for the existence of an entity instance or relation instance
	def process_query(self, query):
		relation, ent1, ent2 = query
		result = 'No'

		if relation in identity:
			if ent2 in self.types and ent1 in self.entities:
				if type(self.entities[ent1]).__name__ == ent2:
					self.apply_spread(ent1)
					result = 'Yes'

		if relation in relations:
			if ent1 in self.entities and ent2 in self.entities:
				if ent1 in getattr(self.entities[ent2], relation) and ent2 in getattr(self.entities[ent1], relation):
					self.apply_spread(ent1)
					self.apply_spread(ent2)
					result = 'Yes'

		return result

	# Increases the activation weight of a given entity by the spread coeff and
	#  also increases the activation weight(s) of all entities that share any binary
	#  relation with the activated entity by spreading coeff * alpha coeff
	def apply_spread(self, entity):
		self.entities[entity].weight += self.spread
		for rel in relations:
			for ent in getattr(self.entities[entity], rel):
				self.entities[ent].weight += self.spread*self.alpha

	# Control
def main(collection_path, spread, alpha):
	db = Knowledge(collection_path, spread, alpha)

if __name__ == "__main__":
    usage = "usage: %prog [options] COLLECTION_PATH"
    parser = OptionParser(usage=usage)

    parser.add_option("-d", "--debug", action="store_true",
                      help="turn on debug mode")

    (options, args) = parser.parse_args()
    # if len(args) != 1:
    # 	print(usage)
    # 	exit(1)
    	
    if options.debug:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig(level=logging.CRITICAL)

    collection, spread, alpha = './', 1, 1
    # collection, spread, alpha = args

    main(collection, spread, alpha)