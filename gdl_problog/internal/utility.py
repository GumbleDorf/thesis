#Class for easily accessing and modifying nested structures with index operators
#obj, must be a mutable structure containing references to other objects
class NestedView(object):
    def __init__(self, obj):
        self.obj = obj
    def set_item_with_index_sequence(self, seq:tuple, value) -> None:
        if len(seq) == 0:
            raise Exception("Index sequence cannot be of length 0")
        self._get_item_internal(seq, self.obj)[seq[len(seq)-1]] = value
    def get_item_with_index_sequence(self, seq:tuple):
        if len(seq) == 0:
            raise Exception("Index sequence cannot be of length 0")
        return self._get_item_internal(seq, self.obj)[seq[len(seq)-1]]
    def _get_item_internal(self, seq: tuple, obj):
        if len(seq) == 1:
            return obj
        else:
            return self._get_item_internal(seq[1:], obj[seq[0]])

