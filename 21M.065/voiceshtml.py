import itertools
from html import ampersand_encode

class WordPart(object):
    def __init__(self, word, start, end):
        self._word = word
        self._start = start
        self._end = end
    pre = property(lambda self: self._word[:self._start])
    part = property(lambda self: self._word[self._start:self._end])
    post = property(lambda self: self._word[self._end:])
    def to_html(self):
        return '<span style="color:gray">%s</span><b>%s</b><span style="color:gray">%s</span>' % (self.pre,
                                  self.part,
                                  self.post)
    def __eq__(self, other):
        return self.pre == other.pre and self.part == other.part and self.post == other.post
    def has_same_word(self, other):
        return self._word == other._word
    def is_compatible_with(self, other):
        return self.has_same_word(other) and self._end == other._start
    def combine(self, other):
        if not self.is_compatible_with(other):
            raise ValueError
        return WordPart(self._word, self._start, other._end)
            
        

class Sound(str):
    def __new__(cls, ipa, orig_pos=None, word_part=None, transliteration=None):
        self = super().__new__(cls, ipa)
        self._orig_pos = orig_pos
        self._word_part = word_part
        self._transliteration = transliteration or ''
        return self
    def _get_original_position(self):
        return self._orig_pos
    original_position = property(_get_original_position)
    def to_html(self, include_ipa=True, include_word_part=True, include_transliteration=True):
        rtn = '<div style="display:inline-block; text-align:left">\n'
        if include_word_part:
            blank_space = '<span style="color:white;">%s</span>' % self._word_part.pre
        else:
            blank_space = ''
        if include_ipa:
            rtn += '<div>%s%s</div>\n' % (blank_space, ampersand_encode(self))
        if include_transliteration:
            rtn += '<div>%s%s</div>\n' % (blank_space, self._transliteration)
        if include_word_part:
            rtn += '<div>%s</div>\n' % self._word_part.to_html()
        rtn += '</div>'
        return rtn
    def is_compatible_with(self, other):
        return self._word_part.is_compatible_with(other._word_part)
    def combine(self, other):
        if not self.is_compatible_with(other):
            raise ValueError
        return Sound(self + other, word_part=self._word_part.combine(other._word_part))
    def reduce_list(cls, sound_list):
        rtn = []
        cur = None
        for sound in sound_list:
            if cur is None:
                cur = sound
            elif cur.is_compatible_with(sound):
                cur = cur.combine(sound)
            else:
                rtn.append(cur)
                cur = sound
        if cur is not None:
            rtn.append(cur)
        return rtn
    reduce_list = classmethod(reduce_list)

def _make_word_parts(word_chunks):
    full_word = ''.join(word_chunks).strip('. ')
    start = 0
    for part in word_chunks:
        end = start + len(part)
        yield WordPart(full_word, start, end)
        start = end

def make_sound_list(ipa_words_chunk_list, words_chunk_list, transliteration_table={}):
    return [Sound(ipa_chunk, i, word_part, (transliteration_table[ipa_chunk] if ipa_chunk in transliteration_table else None))
            for i, (ipa_chunk, word_part) in
            enumerate(itertools.chain(*[zip(ipa, eng) for ipa, eng in zip(ipa_words_chunk_list, map(_make_word_parts, words_chunk_list))]))]
