#!/usr/bin/python3.0
# -*- coding: utf-8 -*-
# python 3
from __future__ import with_statement
import random
import os
import cProfile
from sound import play_sound, combine_wav_files
from ipa import ipa_to_wav, interleave_ipa, close_connection
from voiceshtml import make_sound_list, Sound
    

def paddl(text, char, length):
    if len(text) < length:
        return ''.join(char for i in range(length - len(text))) + text
    else:
        return text

def string_to_tex(unicode):
    return ''.join((s if ord(s) < 127
                   else '\char"%s' % paddl(hex(ord(s))[2:], '0', 4))
                   for s in unicode)

foo="""You turned into a cat! A SMALL cat! You violated Conservation of Energy! That's not just an arbitrary rule, it's implied by the form of the quantum Hamiltonian! Rejecting it destroys unitarity and then you get FTL signaling! And cats are COMPLICATED! A human mind can't just visualize a whole cat's anatomy and, and all the cat biochemistry, and what about the neurology? How can you go on thinking using a cat-sized brain?"""
a="ju tərnd ɪntu ə kæt! ə smɒl kæt! ju vajəletəd kɑnsərveʃən əv ɛnərdʒi! ðæts nɑt dʒəst æn ɑrbətrɛri rul, ɪts ɪmplajd baj ðə fɔrm əv ðə kwɑntəm hamiltonian! rɪdʒɛktɪŋ ɪt dəstrɔjz unitarity ænd ðɛn ju gɛt ftl sɪgnəlɪŋ! ænd kæts ɑr kɑmpləketəd! ə hjumən majnd kænt dʒəst vɪʒwəlɑjz ə hol kæts ənætəmi ænd, ænd ɒl ðə kæt bɑjokɛməstri, ænd wət əbawt ðə nʊrɑlədʒi? haw kæn ju go ɑn θɪŋkəŋ juzɪŋ ə kæt- sajzd bren?"
b="ðɪs ɪz ə sɛlf rəfərɪŋ pis."
c="ðɪ s  ɪ z  ə  s ɛ l f  r ə f ə r ɪ ŋ  p i s."
#http://upodn.com/phon.asp


word_chunks = [word.split(',') for word in 'Th,is is a s,el,f re,ferr,ing pie,ce'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,ɛl,f rə,fər,ɪŋ pi,s'.split(' ')]
d = make_sound_list(ipa_chunks, word_chunks)

word_chunks = [word.split(',') for word in 'Th,is is a re,pea,ted,ly ran,d,om,ly re,a,rran,ged s,e,lf re,ferr,ing s,en,ten,ce'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə rə,pi,təd,li ræn,d,əm,li ri,ə,ren,dʒd s,ɛl,f rə,fər,ɪŋ s,ɛn,tən,s'.split(' ')]
e = make_sound_list(ipa_chunks, word_chunks)

word_chunks = [word.split(',') for word in 'Th,is is a s,e,lf re,ferr,ing ran,d,om,ly s,cr,am,ble,d s,en,ten,ce'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,ɛl,f rə,fər,ɪŋ ræn,d,əm,li s,kr,æm,bəl,d s,ɛn,tən,s'.split(' ')]
f = make_sound_list(ipa_chunks, word_chunks)


word_chunks = [word.split(',') for word in 'Th,is is a s,en,ten,ce ran,d,om,ly s,cr,am,ble,d'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,ɛn,tən,s ræn,d,əm,li s,kr,æm,bəl,d '.split(' ')]
g = make_sound_list(ipa_chunks, word_chunks)


word_chunks = [word.split(',') for word in 'Th,is is a s,en,ten,ce re,pea,ted,ly ran,d,om,ly s,cr,am,ble,d'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,ɛn,tən,s rə,pi,təd,li ræn,d,əm,li s,kr,æm,bəl,d'.split(' ')]
h = make_sound_list(ipa_chunks, word_chunks)


word_chunks = [word.split(',') for word in 'Th,is is a s,en,ten,ce ran,d,om,ly s,cr,am,ble,d'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,ɛn,tən,s ræn,d,əm,li s,kr,æm,bəl,d'.split(' ')]
i = make_sound_list(ipa_chunks, word_chunks)


word_chunks = [word.split(',') for word in 'Th,is is a s,cr,am,ble,d s,en,ten,ce'.split(' ')]
ipa_chunks = [(word + ' ').split(',') for word in 'ð,ɪs ɪz ə s,kr,æm,bəl,d s,ɛn,tən,s'.split(' ')]
j = make_sound_list(ipa_chunks, word_chunks)

print(d)
print(''.join(d))



def is_done(list_of_sound):
    return all(snd.original_position == i for i, snd in enumerate(list_of_sound))

def do_iter(list_of_sound):
    good_pos = [i for i, snd in enumerate(list_of_sound) if snd.original_position == i]
    bad_pos = [i for i, snd in enumerate(list_of_sound) if snd.original_position != i]
    new_pos = dict(zip(bad_pos, random.sample(bad_pos, len(bad_pos))))
    new_pos.update(dict(zip(good_pos, good_pos)))
    return [list_of_sound[new_pos[i]] for i in range(len(list_of_sound))]

def do_iter_n(list_of_sound, n):
    cur = list_of_sound
    so_far = []
    last = ''
    for i in range(n):
        joined_cur = ''.join(cur) + '.  '
        if joined_cur == last:
            return so_far
        else:
            last = joined_cur
        so_far.append(joined_cur)
        cur = do_iter(cur)
    return so_far

def do_iter_both_n(list_of_sound_1, list_of_sound_2, n, person1='Jason', person2='Mario'):
    cur1, cur2 = list_of_sound_1, list_of_sound_2
    files = []
    html = """<!DOCTYPE html>
<html>
<head>
<title>Text-Sound Composition for Jason Gross - %s</title>
</head>
<body>"""
    code = hash((''.join(list_of_sound_1), ''.join(list_of_sound_2)))
    with open(os.path.join(os.getcwd(), 'ipa_only_%d.html' % code), 'w') as ipa_html_f:
        with open(os.path.join(os.getcwd(), 'ipa_translit_%d.html' % code), 'w') as both_html_f:
            def write_both(string):
                ipa_html_f.write(string)
                both_html_f.write(string)
            ipa_html_f.write(html % 'IPA')
            both_html_f.write(html % 'IPA and Corresponding English')
            def done():
                write_both('\n</body>\n</html>')
                return files
            last1, last2 = '', ''
            for i in range(n):
                joined_cur1 = ''.join(cur1) + '.  '
                joined_cur2 = ''.join(cur2) + '.  '
                print(i)
                if joined_cur1 != last1 or joined_cur2 != last2:
                    print(i)
                    filename = interleave_ipa(joined_cur1, joined_cur2, play=False)
                    files.append(filename)
                    write_both("""<div style="display:table;">
<div style="display: table-cell; vertical-align: middle;"><i>%s</i>:&nbsp;</div>
<div style="display: table-cell; vertical-align: middle;">\n""" % person1)
                    ipa_html_f.write('&nbsp;'.join(s.to_html(include_ipa=True, include_word_part=False, include_transliteration=False)
                                                   for s in Sound.reduce_list(cur1)))
                    both_html_f.write('&nbsp;'.join(s.to_html(include_ipa=True, include_word_part=True, include_transliteration=False)
                                                    for s in Sound.reduce_list(cur1)))
                    write_both("""</div>
</div>
<div style="display:table;">
<div style="display: table-cell; vertical-align: middle;"><i>%s</i>:&nbsp;</div>
<div style="display: table-cell; vertical-align: middle;">\n""" % person2)
                    ipa_html_f.write('&nbsp;'.join(s.to_html(include_ipa=True, include_word_part=False, include_transliteration=False)
                                                    for s in Sound.reduce_list(cur2)))
                    both_html_f.write('&nbsp;'.join(s.to_html(include_ipa=True, include_word_part=True, include_transliteration=False)
                                                    for s in Sound.reduce_list(cur2)))
                    write_both('</div>\n</div>\n<hr>\n')
                
                if is_done(cur1) and is_done(cur2):
                    return done()
                last1, last2 = joined_cur1, joined_cur2
                while joined_cur1 == last1 and joined_cur2 == last2:
                    if joined_cur1 == last1:
                        cur1 = do_iter(cur1)
                        joined_cur1 = ''.join(cur1) + '.  '
                    if joined_cur2 == last2:
                        cur2 = do_iter(cur2)
                        joined_cur2 = ''.join(cur2) + '.  '
                #while joined_cur1 == last1 and not is_done(cur1):
                #    cur1 = do_iter(cur1)
                #    joined_cur1 = ''.join(cur1) + '.  '
                #while joined_cur2 == last2 and not is_done(cur2):
                #    cur2 = do_iter(cur2)
                #    joined_cur2 = ''.join(cur2) + '.  '
            return done()

##play_ipa(''.join(d))
##
start1 = random.sample(j, len(j))
start2 = random.sample(j, len(j))
#start1 = random.sample(d, len(d))
#start2 = random.sample(d, len(d))
##print('\n')
##print(start1)
##print(start2)
##print('\n')
files = do_iter_both_n(start1, start2, 40)
combined_name = os.path.join(os.getcwd(), 'full_combined_%s.wav' % hash((''.join(start1), ''.join(start2))))
print('Combining to %s...' % os.path.split(combined_name)[-1])
combine_wav_files(combined_name, *files)
for filename in files:
    print(os.path.split(filename)[-1])
    play_sound(filename)

#play_ipa(do_iter_n(start1,20), 'first_', play=False, voice='mike')
#play_ipa(do_iter_n(start2,20), 'second_', play=False, voice='rich')
##print('Interleaving...')
#import cProfile
#cProfile.run("""
##interleave_wav_files(os.path.join(os.getcwd(), 'combined.wav'),
##                     os.path.join(os.getcwd(), 'first__combined.wav'),
##                     os.path.join(os.getcwd(), 'second__combined.wav'))
#                     """)
##play_sound(os.path.join(os.getcwd(), 'combined.wav'))


if __name__ == '__main__':
    close_connection()
