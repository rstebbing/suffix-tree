##########################################
# File: suffix_tree.py                   #
# Copyright Richard Stebbing 2014.       #
# Distributed under the MIT License.     #
# (See accompany file LICENSE or copy at #
#  http://opensource.org/licenses/MIT)   #
##########################################

# Suffix tree construction using Ukkonen's algorithm
# Refer to: http://stackoverflow.com/questions/9452701/
#   ukkonens-suffix-tree-algorithm-in-plain-english?
# (Responses by jogojapan and makagonov).

# _AccumulatedSuffix
class _AccumulatedSuffix(object):
    def __init__(self, slice_=None):
        self._slice = slice_

    def __add__(self, slice_):
        assert None not in slice_

        if self._slice is None:
            l = 0
        else:
            old_start, old_end = self._slice
            l = old_end - old_start

        start, end = slice_
        return _AccumulatedSuffix((start - l, end))

    def __len__(self):
        if not self._slice:
            return 0

        start, end = self._slice
        return end - start

    def value(self, string):
        if not self._slice:
            return ''

        start, end = self._slice
        return string[start:end]

# _Node
class _Node(object):
    def __init__(self, start=0, end=None, suffix_offset=0):
        self.start = start
        self.end = end
        self.suffix_offset = suffix_offset
        self.suffix_link = 0
        self.children = {}

# SuffixTree
class SuffixTree(object):
    """The SuffixTree class.

    Examples
    --------
    >>> from suffix_tree import SuffixTree
    >>>
    >>> # Construct a complete suffix tree.
    >>> s = SuffixTree()
    >>> print(s.construct('ABCABXABC'))
    0
    >>> print(s.repeats('length'))
    [('ABC', [0, 6]), ('BC', [1, 7]), ('AB', [0, 3, 6])]
    >>>
    >>> # Generate an incomplete suffix tree by disabling auto-termination.
    >>> print(s.construct('ABCABXABC', auto_terminate=False))
    3
    >>> print(s.repeats('length'))
    [('AB', [0, 3])]
    >>>
    >>> # Auto-termination is not always necessary.
    >>> print(s.construct('ABCABXABCD', auto_terminate=False))
    0
    >>> print(s.repeats('length'))
    [('ABC', [0, 6]), ('BC', [1, 7]), ('AB', [0, 3, 6])]
    """

    def __init__(self):
        self._nodes = []
        self._s = ''
        self._string = []

    def construct(self, s, auto_terminate=True):
        """Build the suffix tree using Ukkonen's algorithm.

        Parameters
        ----------
        s : string
            Input string.

        auto_terminate : bool (default=True)
            Automatically terminate the string with '' so that a complete
            suffix tree is guaranteed.

        Returns
        -------
        remainder : int
            The number of characters not included in the suffix tree.
        """
        del self._nodes[:]
        self._nodes.append(_Node())

        self._s = s
        if not self._s:
            return 0

        # Terminate `self._string` to ensure a complete suffix tree is
        # constructed.
        self._string = list(self._s)
        if auto_terminate:
            self._string.append('')

        # _active_point = (active_node, active_edge, active_length)
        self._active_point = (0, '', 0)
        self._suffix_link_required = 0

        remainder = 0
        for step_index in range(len(self._string)):
            remainder += 1

            suffix_start = step_index - remainder + 1
            suffix_end = suffix_start + remainder
            for i in range(remainder):
                if not self._insert(suffix_start + i, suffix_end):
                    break
                remainder -= 1

        if auto_terminate:
            assert remainder == 0, 'remainder != 0 (= %d)' % remainder

        return remainder

    def _insert(self, start, end):
        suffix = self._string[start:end]
        c = suffix[-1]

        # `_get_active_point` ensures Observation 2: That the active length
        # is always strictly less than the length of the active edge.
        active_node, active_edge, active_length = self._get_active_point(
            suffix)
        n = self._nodes[active_node]

        # `internal_node` is used for suffix link creation and resolution.
        internal_node = active_node

        if not active_edge:
            assert active_length == 0
            insert_suffix = c not in n.children
            if not insert_suffix:
                # Observation 1. The final suffix we need to insert is already
                # in the tree.
                self._active_point = (active_node, c, 1)
            else:
                # Insertion at the active node.
                self._nodes.append(_Node(end - 1))
                n.children[c] = len(self._nodes) - 1
        else:
            assert active_length > 0
            n1_index = n.children[active_edge]
            n1 = self._nodes[n1_index]
            insert_suffix = self._string[n1.start + active_length] != c
            if not insert_suffix:
                # Observation 1. The final suffix we need to insert is already
                # in the tree.
                self._active_point = (active_node,
                                      active_edge,
                                      active_length + 1)
            else:
                # Create split node.
                split_suffix_offset = n.suffix_offset + active_length
                new_n1_start = n1.start + active_length
                self._nodes.append(_Node(n1.start,
                                        new_n1_start,
                                        split_suffix_offset))
                ns = self._nodes[-1]
                ns_index = len(self._nodes) - 1

                # Update `n` to point to `ns` instead of `n1`.
                n.children[active_edge] = ns_index

                # Change n1 to start after the split node and adjust its suffix
                # offset.
                n1.start = new_n1_start

                # `n1` is now a child of `ns`.
                c1 = self._string[new_n1_start]
                ns.children[c1] = n1_index

                # Add the additional split child.
                self._nodes.append(_Node(end - 1))
                ns.children[c] = len(self._nodes) - 1

                # Update the internal node used for suffix link resolution.
                internal_node = ns_index

        # Set active point for when a suffix was inserted.
        if insert_suffix:
            if active_node == 0:
                # Rule 1. After an insertion at the root node.
                active_length = max(0, active_length - 1)
                active_edge = suffix[1] if active_length > 0 else ''
                self._active_point = (active_node,
                                      active_edge,
                                      active_length)
            else:
                # Rule 3. Insertion at an internal node so follow
                # suffix link.
                self._active_point = (n.suffix_link,
                                      active_edge,
                                      active_length)

        # Rule 2 / Observation 3. If an internal node has marked a suffix
        # link then set it now.
        if self._suffix_link_required > 0:
            n0 = self._nodes[self._suffix_link_required]
            n0.suffix_link = internal_node

        # Rule 2. Mark the current internal node as requiring a suffix link.
        # If this is root it will be ignored anyway.
        self._suffix_link_required = internal_node if insert_suffix else 0

        return insert_suffix

    def _get_active_point(self, suffix):
        # Observation 2. Ensure that the active point is validly tracking
        # the given suffix.
        active_node, active_edge, active_length = self._active_point
        if active_edge:
            assert active_length > 0

            n = self._nodes[active_node]
            n1_index = n.children[active_edge]
            n1 = self._nodes[n1_index]
            active_suffix_offset = n.suffix_offset
            while active_length > 0 and n1.end is not None and n1.end >= 0:
                edge_length = n1.end - n1.start
                if active_length < edge_length:
                    break

                active_length -= edge_length
                active_suffix_offset += edge_length
                active_node = n1_index
                if active_length == 0:
                    active_edge = ''
                else:
                    # The next edge is selected based on the current
                    # position in the inserting suffix.
                    active_edge = suffix[active_suffix_offset]
                    n1_index = self._nodes[active_node].children[active_edge]
                    n1 = self._nodes[n1_index]

        return active_node, active_edge, active_length

    def repeats(self, sort_by='product'):
        """Return a list of all (potentially overlapping) repeats.

        Parameters
        ----------
        sort_by : string (default='product')
            Key to sort the repeats by (in descending order).
            With `l` denoting the length of a repeat and `n` denoting the
            number of repetitions, the following keys are available:
                'product' : n * l
                'length' : l
                'count' : n

        Returns
        -------
        repeats : list
            Returns a list of tuples, where the first element of each tuple
            is the repeated string and the second element is a list of
            offsets where the repetition occurs.
        """
        if not self._s or not self._nodes:
            return []

        # Build `accumulated_suffixes` by descending the tree and accumulating
        # the suffixes along each edge to each child node.
        # Save `parent_nodes` so that the number of descendant leaves can
        # be propagated upstream afterwards.
        num_nodes = len(self._nodes)
        accumulated_suffixes = [_AccumulatedSuffix() for _ in range(num_nodes)]
        nodes_to_process = [0]
        parent_nodes = [None] * num_nodes
        while nodes_to_process:
            i = nodes_to_process.pop(0)
            for j in self._nodes[i].children.values():
                # Save `accumulated_suffixes` for child node `j`.
                n = self._nodes[j]
                accumulated_suffixes[j] = (accumulated_suffixes[i] +
                    (n.start, len(self._s) if n.end is None else n.end))
                # Save parent and process child next.
                parent_nodes[j] = i
                nodes_to_process.append(j)

        # The accumulated suffix at each internal marks a repeated subsequence,
        # and the number of times it is repeated is equal to the number of
        # descendant leaf nodes.
        # Build `descendants` by propagating the leaf nodes up the tree.
        descendants = [[] for _ in range(num_nodes)]
        number_of_children_processed = [0] * num_nodes
        def append_upstream(i):
            j = parent_nodes[i]
            if j is None:
                return
            descendants[j].extend(descendants[i])
            number_of_children_processed[j] += 1
            if number_of_children_processed[j] >= len(self._nodes[j].children):
                append_upstream(j)
        for i, n in enumerate(self._nodes):
            if len(n.children) <= 0:
                # Leafs have 1 descendant (themselves) by definition.
                descendants[i].append(i)
                append_upstream(i)

        # We count a repeat node as an internal node with an accumulated
        # suffix of at least length 2.
        repeat_nodes = []
        for i, n in enumerate(self._nodes):
            if n.children and len(accumulated_suffixes[i]) >= 2:
                repeat_nodes.append(i)

        # Sort the repeats in descending order.
        if sort_by == 'product':
            key = lambda i: len(accumulated_suffixes[i]) * len(descendants[i])
        elif sort_by == 'length':
            key = lambda i: len(accumulated_suffixes[i])
        elif sort_by == 'count':
            key = lambda i: len(descendants[i])
        else:
            raise ValueError('unknown `sort_by` option "%s"' % sort_by)
        repeat_nodes = sorted(repeat_nodes, key=key)[::-1]

        # For each repeated string, store the offsets into the global
        # string.
        repeats = []
        for i in repeat_nodes:
            offsets = []
            for j in descendants[i]:
                # Descendants should only be leaf nodes.
                assert self._nodes[j].end is None
                offsets.append(len(self._s) - len(accumulated_suffixes[j]))
            repeats.append((accumulated_suffixes[i].value(self._s),
                            sorted(offsets)))
        return repeats

    def graphviz_export(self, output_path,
                        show_node_index=False,
                        no_suffix_links_on_edges=True):
        """Export the suffix tree as an image using graphviz.

        Parameters
        ----------
        output_path : string
            Destination path for the image. If no extension is present, '.png'
            is automatically appended.

        show_node_index : bool (default=False)
            Display the node index.

        no_suffix_links_on_edges : bool (default=True)
            Display the suffix links.

        Returns
        -------
        output_path : string or None
            The destination path (with extension appended if required) on
            success.
        """
        if not self._s or not self._nodes:
            return

        import os
        import pygraphviz
        g = pygraphviz.AGraph()

        for i, n in enumerate(self._nodes):
            node_string = str(i)
            if n.children:
                g.add_node(node_string,
                           label=node_string if show_node_index else '',
                           style='filled',
                           fillcolor='lightgrey',
                           shape='circle',
                           width=0.1,
                           height=0.1)
            else:
                g.add_node(node_string,
                           label=node_string if show_node_index else '',
                           shape='circle' if show_node_index else 'point')

        make_edge = lambda i, j: (i, j) if i < j else (j, i)

        edges = set()
        for i, n in enumerate(self._nodes):
            sorted_keys = sorted(n.children.keys())
            for key in sorted_keys:
                n1_index = n.children[key]
                n1 = self._nodes[n1_index]
                label = self._s[n1.start:n1.end]
                g.add_edge(str(i), str(n1_index), label=label)

                edges.add(make_edge(i, n1_index))

        for i, n in enumerate(self._nodes):
            if n.suffix_link != 0:
                # Don't overwrite a regular edge with a suffix link.
                if (not no_suffix_links_on_edges or
                        make_edge(i, n.suffix_link) not in edges):
                    g.add_edge(str(i), str(n.suffix_link), style='dotted')

        g.layout()

        # Add '.png' extension if required.
        head, tail = os.path.split(output_path)
        root, ext = os.path.splitext(tail)
        if not ext:
            ext = '.png'
        output_path = os.path.join(head, root + ext)
        g.draw(output_path, prog='dot')

        return output_path

if __name__ == '__main__':
    import unittest
    from collections import defaultdict

    # naive_repeats
    def naive_repeats(s):
        """Return a dictionary of all (potentially overlapping) repeats."""
        n = len(s)

        substring_to_repeat_indices = defaultdict(set)
        for i in range(n):
            for j in range(i + 2, n):
                s1 = s[i:j]
                n1 = len(s1)
                for k in range(i + 1, n):
                    if s[k:k + n1] == s1:
                        substring_to_repeat_indices[s1].add(i)
                        substring_to_repeat_indices[s1].add(k)

        repeat_indices_to_substring = {}
        for k, v in substring_to_repeat_indices.items():
            v = tuple(sorted(v))
            try:
                k1 = repeat_indices_to_substring[v]
            except KeyError:
                assign = True
            else:
                assign = len(k) > len(k1)

            if assign:
                repeat_indices_to_substring[v] = k

        return {v:list(k) for k,v in repeat_indices_to_substring.items()}

    # TestSuffixTree
    class TestSuffixTree(unittest.TestCase):
        def test_construct(self):
            self.assertEqual(0, SuffixTree().construct('ABC'))
            self.assertEqual(0, SuffixTree().construct('ABCA'))
            self.assertEqual(1, SuffixTree().construct('ABCA',
                                                       auto_terminate=False))
            self.assertEqual(3, SuffixTree().construct('ABCABC',
                                                       auto_terminate=False))
            self.assertEqual(0, SuffixTree().construct('ABCABCD',
                                                       auto_terminate=False))

        def test_repeats(self):
            for s in ['ABAB', 'ABCABXABCD', 'CDDDCDC', 'CDDDCDCDDDCD']:
                t = SuffixTree()
                t.construct(s)
                self.assertEqual(naive_repeats(s), dict(t.repeats()))

    unittest.main()
