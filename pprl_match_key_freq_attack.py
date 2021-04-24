# Privacy attack on PPRL Match-key approach using frequency distributions
#
# Anushka Vidanage, Thilina Ranbaduge, Peter Christen, and Sean Randall
# January 2020
#
# Copyright 2020 Australian National University and others.
# All Rights reserved.
#
# -----------------------------------------------------------------------------
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# -----------------------------------------------------------------------------
#
# Usage:
#   python pprl-match-key-attack.py [encode_data_set_name] [encode_rec_id_col] 
#                       [encode_col_sep_char] [encode_header_line_flag]
#                       [plain_data_set_name][plain_rec_id_col][plain_col_sep_char]
#                       [plain_header_line_flag] [sample_size] [run_method]
#                       [min_weight_score][attacker_knwlge][attack_step]
#                       [consdrd_top_num_val]
#
# where:
# encode_data_set_name      is the name of the CSV file to be encoded into BFs
# encode_rec_id_col         is the column in the CSV file containing record
#                           identifiers
# encode_col_sep_char       is the character to be used to separate fields in
#                           the encode input file
# encode_header_line_flag   is a flag, set to True if the file has a header
#                           line with attribute (field) names
# plain_data_set_name       is the name of the CSV file to use plain text
#                           values from
# plain_rec_id_col          is the column in the CSV file containing record
#                           identifiers
# plain_col_sep             is the character to be used to separate fields in
#                           the plain text input file
# plain_header_line_flag    is a flag, set to True if the file has a header
#                           line with attribute (field) names
# sample_size               is the sample size in percentage if the attack
#                           is just performed on a sample of the data
# run_method                is the name of the method that should run
#                            - linkage: Run the linkage on two datasets
#                                       based on match-key approach
#                            - attack: perform the attack on encoded
#                                      dataset
# min_weight_score
# attacker_knwlge           is a string that defines the knowledge level
#                           of the attacker
#                            - Comb: Attacker knows the attribute combinations
#                                    (match-keys) used for the encoding
#                            - Attr: Attacker knows only the attributes used
#                                    to generate match-keys
#                            - Dom:  Attacker does not know anything about the
#                                    encoding parameters, only the domain knowledge
#                                    that the plain-text database has similar
#                                    characteristics to the encoded database
# attack_step                is a string that defines which steps of the attack
#                            that need to be performed.
#                             - main: First four steps of the attack where we
#                                     identify the attribute combinations used
#                                     for each encoded match-key
#                             - re-ident: The plain-text re-identification step.
#                                         Last step of the attack
# consdrd_top_num_val        is the number of values to consider when measuring 
#                            precision/recall (precision at k). This is only used
#                            if we are measuring precision at k. Otherwise this
#                            parameter is not used.
#
# Note that if the plain text data set is the same as the encode data set
# (with the same attributes) then the encode data set will also be used as the
# plain text data set.

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

MAX_MEMORY_USE = 300000  # In Megabytes

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

# Standard library imports
import csv
import gzip
import math
import hashlib
import hmac
import os.path
import socket
import random
import sys
import time
import itertools
import numpy
import zlib
from scipy import stats
import matplotlib.pyplot as plt
from scipy.interpolate import spline

# Extra modules
from libs import auxiliary 

HMAC_KEY_LEN = 16
HMAC_HEX_KEY = 'matchKeyAttack' # ''.join(random.choice('0123456789abcdef') for _ in range(HMAC_KEY_LEN))

BF_HASH_FUNCT1 = hashlib.sha1
BF_HASH_FUNCT2 = hashlib.md5
BF_HASH_FUNCT3 = hashlib.sha224

today_str = time.strftime("%Y%m%d", time.localtime())
                   
# Constant values to use in the plotting function
#
ASPECT_RATIO = 0.4    # 0.27 # aspect ratio of the plots
FILE_FORMAT  = '.eps' #'.png'

PLT_FONT_SIZE    = 20 # 28 # used for axis lables and ticks
LEGEND_FONT_SIZE = 18 # 28 # used for legends
TITLE_FONT_SIZE  = 28 # 30 # used for plt title
TICKS_FONT_SIZE  = 15
X_TICKS_FONT_SIZE= 10

ATTR_SELECT_DICT = {'NCVR_FULL':{'ENC_ATTR_LABELS': 
                                ['ncid', 'voter_reg_num', 'status_code', 
                                 'reason_code', 'name_prefix', 'first_name', 
                                 'middle_name', 'last_name', 'name_suffix', 
                                 'age', 'birth_year', 'gender', 'race', 
                                 'ethnic', 'street_address', 'city', 'state', 
                                 'zip_code', 'full_phone_num', 'drivers_license', 
                                 'birth_place', 'register_date', 'county_desc', 
                                 'party_cd'],
                                #
                                'REMOVE_ATTR_LIST': 
                                [0, 1, 2, 3, 4, 8, 9, 11, 12, 13, 15, 16, 18, 
                                 19, 20, 21, 22, 23],
                                #
                                'ATTCK_ATTR_LIST': 
                                [5, 6, 7, 10, 11, 12, 14, 15, 16, 17],
                                #
                                'BLK_ATTR_LIST':
                                [5,7,11],
                                #
                                'ENC_ATTR_NAMES_DICT': 
                                {0:'ID', 1:'RG', 2: 'SC', 3: 'RC', 4:'PF', 
                                 5:'FN', 6:'MN', 7:'LN', 8:'SF', 9:'AG', 
                                 10:'BY', 11:'GD', 12:'RC', 13:'EC', 14:'SA', 
                                 15:'CT', 16:'ST', 17:'ZP', 18:'PH', 19:'BP', 
                                 20:'RD', 21:'CD', 22:'PD'}},
                    # 
                    'NCVR_BAL':{'ENC_ATTR_LABELS': 
                                ['voter_id', 'first_name', 'middle_name', 
                                 'last_name', 'age', 'gender', 
                                 'street_address', 'city', 'state', 
                                 'zip_code', 'full_phone_num'],
                                #
                                'REMOVE_ATTR_LIST': 
                                [0, 4, 5, 8],
                                #
                                'ATTCK_ATTR_LIST':
                                [3, 4, 5, 9, 12, 13, 14, 15,],
                                #
                                'BLK_ATTR_LIST':
                                [3,5],
                                #
                                'ENC_ATTR_NAMES_DICT': 
                                {0:'ID', 1:'FN', 2:'MN', 3:'LN', 4:'AG', 
                                 5:'GN', 6:'SA', 7:'CT', 8:'ST', 9:'ZP', 
                                 10:'PH'}},
                    #
                    'NCVR_50':{'ENC_ATTR_LABELS': 
                                ['voter_id', 'voter_reg_num', 'name_prefix', 
                                 'first_name', 'middle_name', 'last_name', 
                                 'name_suffix', 'age', 'birth_year', 'gender', 
                                 'race', 'ethnic', 'street_address', 'city', 
                                 'state', 'zip_code', 'full_phone_num', 
                                 'birth_place', 'register_date'],
                                #
                                'REMOVE_ATTR_LIST': 
                                [0, 1, 2, 6, 7, 9, 10, 11, 13, 14, 16, 17, 
                                 18],
                                #
                                'ATTCK_ATTR_LIST':
                                [3, 4, 5, 8, 9, 12, 13, 14, 15,],
                                #
                                'BLK_ATTR_LIST':
                                [3,5,9],
                                #
                                'ENC_ATTR_NAMES_DICT': 
                                {0:'ID', 1:'RG', 2:'PF', 3:'FN', 4:'MN', 
                                 5:'LN', 6:'SF', 7:'AG', 8:'BY', 9:'GD', 
                                 10:'RC', 11:'EC', 12:'SA', 13:'CT', 14:'ST', 
                                 15:'ZP', 16:'PH', 17:'BP', 18:'RD'}},
                    #
                    'MVR_FULL':{'ENC_ATTR_LABELS': 
                                ['last_name', 'first_name', 'middle_name', 
                                 'name_suffix', 'birthyear', 'gender', 
                                 'date_of_registration', 'house_number_character', 
                                 'residence_street_number', 'house_suffix', 
                                 'pre-direction', 'street_name', 'street_type', 
                                 'suffix_direction', 'residence_extension', 
                                 'city', 'state', 'zipcode', 'mail_address_1', 
                                 'mail_address_2', 'mail_address_3', 
                                 'mail_address_4', 'mail_address_5', 
                                 'voter_id', 'county_code', 'jurisdiction', 
                                 'ward_precinct', 'school_code', 'state_house', 
                                 'state_senate', 'us_congress', 
                                 'county_commissioner', 'village_code', 
                                 'village_precinct', 'school_precinct', 
                                 'permanent_absentee_ind', 'status_type', 
                                 'uocava_status'],
                                #
                                'REMOVE_ATTR_LIST': 
                                [3, 6, 7, 9, 10, 12, 13, 14, 18, 19, 20, 21, 
                                 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
                                 34, 35, 36, 37, 5, 15, 16, ],
                                #
                                'ATTCK_ATTR_LIST':
                                [0, 1, 2, 4, 8, 11, 16, 17], #[0, 1, 2, 4, 5, 8, 11, 15, 16, 17],
                                #
                                'BLK_ATTR_LIST':
                                [0, 1, 5],
                                #
                                'ENC_ATTR_NAMES_DICT': 
                                {0:'LN', 1:'FN', 2:'MN', 3:'SF', 4:'BY', 
                                 5:'GD', 6:'DR', 7:'HN', 8:'RS', 9:'HSF', 
                                 10:'PD', 11:'SN', 12:'ST', 13:'SD', 14:'RE', 
                                 15:'CT', 16:'ST', 17:'ZP', 18:'MA1', 19:'MA2', 
                                 20:'MA3', 21:'MA4', 22:'MA5', 23:'ID', 24:'CD',
                                 25:'JD', 26:'WP', 27:'SC', 28:'SH', 29:'SS', 
                                 30:'UC', 31:'CC', 32:'VC', 33:'VP', 34:'SP', 
                                 35:'PAI', 36:'STT', 37:'US'}},
                    }

# -----------------------------------------------------------------------------

def load_data_set_extract_attr_val(file_name, rec_id_col, col_sep_char, 
                                   header_line, attr_list, sample_size):
  
  """Load the given file, extract all attributes and get them into a single 
     dictionary. 

     Returns:
     1) a dictionary of record values where keys are record ids and values
        are all the attribute values of that record.
     2) a list of the attribute names in the dataset
     3) a list of missiga value percentages for each attribute
     4) a dictionary of unique values for each selected attribute 
  """
  
  start_time = time.time()
  
  data_dict = {}
  unique_val_id_dict = {}

  if (file_name.endswith('gz')):
    f = gzip.open(file_name)
  else:
    f = open(file_name)
    
  print
  print 'Load data set from file:', file_name
  print '  Attribute separator: %c' % (col_sep_char)

  csv_reader = csv.reader(f, delimiter=col_sep_char)
  
  if (header_line == True):
    header_list = csv_reader.next()
    print '  Header line:', header_list

  new_header_list = []
  for attr_index in attr_list:
    attr_lablel = header_list[attr_index]
    new_header_list.append(attr_lablel)
  
  header_list = new_header_list
  del new_header_list
  
  print '  New header line:', header_list
  
  # Check if birth year need to be calculated for the dataset
  age_calc = False
  if('2011' in file_name or '2017' in file_name):
    
    if('500000' in file_name and 8 in attr_list):
      age_attr_index = 7
      birth_year_attr_index = 8
      age_calc = True
      base_year = 2011 if ('2011' in file_name) else 2017
    elif('balanced' not in file_name and 10 in attr_list):
      age_attr_index = 9
      birth_year_attr_index = 10
      age_calc = True
      base_year = 2011 if ('2011' in file_name) else 2017
  
  rec_num = 0
  num_duplicates = 0
  num_missing_val_list = [0 for _ in range(len(header_list))]
  
  # Check if sampling is needed and then sample the dataset
  if(sample_size != 100):
    num_rec = sum(1 for rec in csv.reader(gzip.open(file_name), delimiter=col_sep_char))
    
    sample_num_rec = int(num_rec*(float(sample_size)/100))
    
    sample_rec_num_set = set(random.sample(xrange(num_rec), sample_num_rec))
    
    print
    print '  Sample size:', len(sample_rec_num_set)
  else:
    sample_rec_num_set = set()
  
  for (j, data_rec) in enumerate(csv_reader):
    
    # Check if record number is in sample
    if(sample_size != 100 and j not in sample_rec_num_set):
      continue
    
    rec_num += 1

    if (rec_num % 1000000 == 0):
      time_used = time.time() - start_time
      print '  Processed %d records in %d sec (%.2f msec average)' % \
            (rec_num, time_used, 1000.0*time_used/rec_num)
      print '   ', auxiliary.get_memory_usage()

      auxiliary.check_memory_use(MAX_MEMORY_USE)
    
    # Get record ID
    rec_id = data_rec[rec_id_col].strip().lower()
    if '-' in rec_id:
      rec_id = rec_id.split('-')[1].strip()
      
    if(rec_id in data_dict):
      num_duplicates += 1
    else:
      # A list of attribute values per record
      rec_val_list      = []
      
      # Loop over each attribute value in the record
      for (i, attr_index) in enumerate(attr_list):
        attr_val = data_rec[attr_index]
        
        attr_val = attr_val.strip().lower()
        
        if(age_calc and birth_year_attr_index == attr_index):
          age_val = data_rec[age_attr_index]
          
          if(age_val == ' ' or len(age_val) == 0):
            attr_val = ''
          else:
            age_val = int(age_val)
            new_by_val = base_year - age_val
            attr_val = str(new_by_val)
        
        if(attr_val == ' ' or len(attr_val) == 0):
          num_missing_val_list[i] += 1
        
        rec_val_list.append(attr_val)
        
        # Update unique values id dictionary
        #
        if(attr_val != ' ' and len(attr_val) != 0):
          attr_id_dict = unique_val_id_dict.get(i, {})
          val_id_set   = attr_id_dict.get(attr_val, set())
          val_id_set.add(rec_id)
          
          attr_id_dict[attr_val] = val_id_set
          unique_val_id_dict[i] = attr_id_dict
          
      assert len(rec_val_list) == len(header_list), (len(rec_val_list), 
                                                     len(header_list))
      data_dict[rec_id] = rec_val_list
  
  time_used = time.time() - start_time
  print '  Processed %d records in %d sec (%.2f msec average)' % \
        (rec_num, time_used, 1000.0*time_used/rec_num)
  print '   ', auxiliary.get_memory_usage()
  print
  print '  Number of duplicate records found: %d' %num_duplicates
  print
  print '  Missing value percentages'
  
  total_rec = len(data_dict)
  
  missing_val_perc_list = []
  
  for i, num_missing in enumerate(num_missing_val_list):
    missing_perc = 100 * float(num_missing)/total_rec
    missing_val_perc_list.append(missing_perc)
    print '  - %s : %.2f %%' %(header_list[i], missing_perc)
  
  print
  assert total_rec+num_duplicates == rec_num, \
  (total_rec+num_duplicates, rec_num)
  
  return data_dict, header_list, missing_val_perc_list, unique_val_id_dict

# -----------------------------------------------------------------------------

def attr_blocking(data_dict, blk_attr_list):
  
  data_blk_dict = {}  # The dictionary with blocks to be generated and returned
  
  for (rec_id, rec_values) in data_dict.items():

    rec_bkv = ''  # Initialise the blocking key value for this record

    # Process selected blocking attributes
    #
    for attr in blk_attr_list:
      attr_val = rec_values[attr]
      
      blk_dict = data_blk_dict.get(attr, {})
      
      rec_id_set = blk_dict.get(attr_val, set())
      rec_id_set.add(rec_id)
      blk_dict[attr_val] = rec_id_set
      data_blk_dict[attr] = blk_dict

  return data_blk_dict

# -----------------------------------------------------------------------------

def phoneticBlocking(rec_dict, blk_attr_list):
  """Build the blocking index data structure (dictionary) to store blocking
     key values (BKV) as keys and the corresponding list of record identifiers.

     A blocking is implemented that concatenates Soundex encoded values of
     attribute values.

     Parameter Description:
       rec_dict      : Dictionary that holds the record identifiers as keys
                       and corresponding list of record values
       blk_attr_list : List of blocking key attributes to use

     This method returns a dictionary with blocking key values as its keys and
     list of record identifiers as its values (one list for each block).
  """

  block_dict = {}  # The dictionary with blocks to be generated and returned

  print('Run phonetic blocking:')
  print('  List of blocking key attributes: '+str(blk_attr_list))
  print('  Number of records to be blocked: '+str(len(rec_dict)))
  print('')

  for (rec_id, rec_values) in rec_dict.items():

    rec_bkv = ''  # Initialise the blocking key value for this record

    # Process selected blocking attributes
    #
    for attr in blk_attr_list:
      attr_val = rec_values[attr]

      if (attr_val == ''):
        rec_bkv += 'z000'  # Often used as Soundex code for empty values

      else:  # Convert the value into its Soundex code

        attr_val = attr_val.lower()

        sndx_val = attr_val[0]  # Keep first letter

        for c in attr_val[1:]:  # Loop over all other letters

          if (c in 'aehiouwy'):  # Not inlcuded into Soundex code
            pass
          elif (c in 'bfpv'):
            if (sndx_val[-1] != '1'):  # Don't add duplicates of digits
              sndx_val += '1'
          elif (c in 'cgjkqsxz'):
            if (sndx_val[-1] != '2'):  # Don't add duplicates of digits
              sndx_val += '2'
          elif (c in 'dt'):
            if (sndx_val[-1] != '3'):  # Don't add duplicates of digits
              sndx_val += '3'
          elif (c in 'l'):
            if (sndx_val[-1] != '4'):  # Don't add duplicates of digits
              sndx_val += '4'
          elif (c in 'mn'):
            if (sndx_val[-1] != '5'):  # Don't add duplicates of digits
              sndx_val += '5'
          elif (c in 'r'):
            if (sndx_val[-1] != '6'):  # Don't add duplicates of digits
              sndx_val += '6'

        if (len(sndx_val) < 4):
          sndx_val += '000'  # Ensure enough digits

        sndx_val = sndx_val[:4]  # Maximum length is 4

        rec_bkv += sndx_val

    # Insert the blocking key value and record into blocking dictionary
    #
    if (rec_bkv in block_dict): # Block key value in block index

      # Only need to add the record
      #
      rec_id_list = block_dict[rec_bkv]
      rec_id_list.append(rec_id)

    else: # Block key value not in block index

      # Create a new block and add the record identifier
      #
      rec_id_list = [rec_id]

    block_dict[rec_bkv] = rec_id_list  # Store the new block

  return block_dict

# -----------------------------------------------------------------------------

def pairs_completeness(data_blk_dict_a, data_blk_dict_b,  true_match_id_set):
  """Pairs completeness measures the effectiveness of a blocking technique in
     the record linkage process.

     Pairs completeness is calculated as the number of true matches included in
     the candidate record pairs divided by the number of all true matches.

     Parameter Description:
       data_blk_dict_a/b : A dictionary of candidate records output
                         by a blocking technique
       true_match_set  : Set of true matches (record identifier pairs)

     The method returns a float value.
  """
  
  ident_true_rec = set()
  cand_rec_id_pairs = set()
    
  for attr in data_blk_dict_a.keys():
    
    if(attr in data_blk_dict_b):
      
      attr_id_set_a = data_blk_dict_a[attr]
      attr_id_set_b = data_blk_dict_b[attr]
      
      for rec_id in attr_id_set_a:
        if(rec_id in attr_id_set_b and rec_id in true_match_id_set):
          ident_true_rec.add(rec_id)
      
      #cand_rec_pair_set = set(zip(attr_id_set_a, attr_id_set_b))
      cand_rec_pair_obj = itertools.product(attr_id_set_a, attr_id_set_b)
      
      for id_pair in cand_rec_pair_obj:
        cand_rec_id_pairs.add(id_pair)
          
        # Set addition is much faster than the set union
        #cand_rec_id_pairs = cand_rec_id_pairs.union(cand_rec_pair_set)
  
  pc = float(len(ident_true_rec))/len(true_match_id_set)  # Replace with your code
  
  return pc, cand_rec_id_pairs

# -----------------------------------------------------------------------------

def get_attr_comb_above_thresh(attr_weight_dict, min_weight_score):
  
  attr_index_list = attr_weight_dict.keys()
  attr_list = attr_weight_dict.keys()
  
  num_attr = len(attr_list)
  
  attr_flag_comb_obj = list(itertools.product([0, 1], repeat=num_attr))
  
  ident_attr_comb_list = []
  final_attr_comb_list = []
  
  for attr_flag_comb in attr_flag_comb_obj:
    
    total_score = 0.0
    agree_set = set()
    
    for flag_index, flag_val in enumerate(attr_flag_comb):
      
      attr_index = attr_list[flag_index]
      
      if(flag_val == 1):
        agree_weight = attr_weight_dict[attr_index][0]
        total_score += agree_weight
        agree_set.add(attr_index)
      elif(flag_val == 0):
        disagree_weight = attr_weight_dict[attr_index][1]
        total_score += disagree_weight
    
    if(total_score >= min_weight_score):
      
      # Check for supersets do superset pruning
      #
      if(any(ident_comb.issubset(agree_set) for ident_comb in ident_attr_comb_list)):
        continue
      else:
        ident_attr_comb_list.append(agree_set)
  
  for attr_comb in ident_attr_comb_list:
    final_attr_comb_list.append(sorted(attr_comb))
  
  return final_attr_comb_list

# -----------------------------------------------------------------------------

def calculate_agree_disagree_weights(enc_data_dict, plain_data_dict, 
                                     enc_unique_val_dict,plain_unique_val_dict,
                                     consider_attr_num_list, sample_size = None):
  
  start_time = time.time()
  
  u_prob_approx = False
  
  enc_rec_id_set   = set(enc_data_dict.keys())
  plain_rec_id_set = set(plain_data_dict.keys())

  if(sample_size != None):
    random.seed(random.randint(0, sys.maxint))
    
    enc_rec_id_sample   = set(random.sample(enc_rec_id_set, sample_size))
    plain_rec_id_sample = set(random.sample(plain_rec_id_set, sample_size))
    
    common_rec_id_set = enc_rec_id_sample.intersection(plain_rec_id_sample)
    common_rec_perc = 100*float(len(common_rec_id_set))/len(enc_rec_id_sample)
  
  else:
    common_rec_id_set = enc_rec_id_set.intersection(plain_rec_id_set)
    common_rec_perc = 100*float(len(common_rec_id_set))/len(enc_rec_id_set)

  print 'Number of records common to both datasets: %d (%.2f%%)' %(len(common_rec_id_set), common_rec_perc)
  print
  
  m_prob_dict = {}
  u_prob_dict = {}
  
  m_count_dict = {}
  u_count_dict = {}
  
  attr_weight_dict = {}
  
  for common_rec_id in common_rec_id_set:
    
    enc_rec_val_list   = enc_data_dict[common_rec_id]
    plain_rec_val_list = plain_data_dict[common_rec_id]
    
    for attr_num in consider_attr_num_list:
      
      if(enc_rec_val_list[attr_num] == plain_rec_val_list[attr_num]):
        m_count_dict[attr_num] = m_count_dict.get(attr_num, 0) + 1
    
  num_common_rec = len(common_rec_id_set)
  
  for attr_num, attr_count in m_count_dict.iteritems():
    m_prob_dict[attr_num] = float(attr_count)/num_common_rec
   
  print 'm-probability values', m_prob_dict
  
  time_used = time.time() - start_time
  print '  Calculated m-probability values in %d sec' %time_used
  print '   ', auxiliary.get_memory_usage()
  auxiliary.check_memory_use(MAX_MEMORY_USE)
  
  # Calculate u-probabilities
  #
  for attr_index in consider_attr_num_list:
     
    enc_val_dict   = enc_unique_val_dict[attr_index]
    plain_val_dict = plain_unique_val_dict[attr_index]
    
    if(u_prob_approx):
      
      num_unique_val = len(enc_val_dict.keys())
      u_porb = float(1)/num_unique_val
      
      u_prob_dict[attr_index] = u_porb
    
    else:
       
      for attr_val in enc_val_dict.keys():
         
        if(attr_val in plain_val_dict):
           
          enc_id_set = enc_val_dict[attr_val]
          plain_id_set = plain_val_dict[attr_val]
           
          comm_id_set = enc_id_set.intersection(plain_id_set)
           
          num_enc_id   = len(enc_id_set)
          num_plain_id = len(plain_id_set)
          num_comm_id  = len(comm_id_set)
          
          non_match_pairs = (num_enc_id*num_plain_id) - num_comm_id
         
          u_count_dict[attr_index] = u_count_dict.get(attr_index, 0) + non_match_pairs
     
  
  total_non_match_pairs = (len(enc_rec_id_set)*len(plain_rec_id_set)) - len(common_rec_id_set)
  total_pairs = len(enc_rec_id_set)*len(plain_rec_id_set)
  
  if(u_prob_approx == False):
    for attr_num, attr_count in u_count_dict.iteritems():
      joint_prob = float(attr_count)/total_pairs
      marginal_prob = float(total_non_match_pairs)/total_pairs
      
      cond_prob  = joint_prob/marginal_prob
      u_prob_dict[attr_num] = cond_prob
      #u_prob_dict[attr_num] = numpy.mean(attr_prob_list)
  
  print
  print 'u-probability values', u_prob_dict
   
  time_used = time.time() - start_time
  print '  Calculated u-probability values in %d sec' %time_used
  print '   ', auxiliary.get_memory_usage()
  auxiliary.check_memory_use(MAX_MEMORY_USE) 
   
  print
  
  for attr_index in consider_attr_num_list:
    
    if(attr_index in m_prob_dict):
      attr_m_prob = m_prob_dict[attr_index]
    else:
      attr_m_prob = 0.0
      
    if(attr_index in u_prob_dict):
      attr_u_porb = u_prob_dict[attr_index]
    else:
      attr_u_porb = 0.0
    
    # Prevent division by 0 errors
    if(attr_u_porb == 0.0):
      agree_val = 0.0
    else:
      agree_val    = float(attr_m_prob)/attr_u_porb
    
    # Prevent division by 0 errors  
    if(attr_u_porb == 1.0):
      disagree_val = 0.0
    else:
      disagree_val = float(1 - attr_m_prob)/(1 - attr_u_porb)
    
    if(agree_val == 0.0):
      attr_agree_weight = 0.0
    else:
      attr_agree_weight    = math.log(agree_val, 10)
      
    if(disagree_val == 0.0):
      attr_disagree_weight = 0.0
    else:
      attr_disagree_weight = math.log(disagree_val, 10)
    
    attr_weight_dict[attr_index] = [attr_agree_weight, attr_disagree_weight]
  
  return attr_weight_dict
      

# -----------------------------------------------------------------------------

def get_same_diff_val_count(enc_data_dict, plain_data_dict, true_match_id_set, 
                            attr_list):
  
  
  attr_same_diff_count_dict = {}
  match_key_same_diff_count_dict = {}
  num_missing_val_dict = {}
    
  for match_id in true_match_id_set:
  
    enc_rec_val_list   = enc_data_dict[match_id]
    plain_rec_val_list = plain_data_dict[match_id]
    
    for i in range(len(enc_rec_val_list)):
      
      enc_rec_val = enc_rec_val_list[i]
      plain_rec_val = plain_rec_val_list[i]
      
      if(enc_rec_val != ' ' and len(enc_rec_val) != 0 and \
         plain_rec_val != ' ' and len(plain_rec_val) != 0):
        
        attr_label = attr_list[i]
        
        same_diff_list = attr_same_diff_count_dict.get(attr_label, [0, 0])
        
        if(enc_rec_val != plain_rec_val):
          same_diff_list[1] += 1
        else:
          same_diff_list[0] += 1
        
        attr_same_diff_count_dict[attr_label] = same_diff_list    
    
  
  return attr_same_diff_count_dict, match_key_same_diff_count_dict           

# -----------------------------------------------------------------------------

def create_match_key_dict(enc_data_dict, attr_comb_list):
  
  enc_match_key_dict = {}
  unique_match_key_dict = {}
  
  # Sort attribute combination list based on number of
  # attributes
  sorted_attr_comb_list = sorted(attr_comb_list, key=lambda x: len(x), reverse=True)
  
  for attr_comb in sorted_attr_comb_list:
    
    attr_comb_match_key_dict = {}
    
    for rec_id, rec_list in enc_data_dict.iteritems():
      
      if(all(rec_list[attr_index] != ' ' and len(rec_list[attr_index]) != 0 for attr_index in attr_comb)):
        
        concat_string = ','.join(rec_list[attr_index] for attr_index in attr_comb)
        
        hash_val = hmac.new(HMAC_HEX_KEY, concat_string, hashlib.sha1)
        
        match_key = hash_val.hexdigest().decode("hex").encode("base64")[0:15]
          
        if(match_key in attr_comb_match_key_dict):
          rec_id_set = attr_comb_match_key_dict[match_key]
          rec_id_set.add(rec_id)
          attr_comb_match_key_dict[match_key] = rec_id_set
        else:
          rec_id_set = set([rec_id])
          attr_comb_match_key_dict[match_key] = rec_id_set
          
        # Update unique match-key dictionary
        if(match_key in unique_match_key_dict):
          plain_text_val = unique_match_key_dict[match_key] 
          assert plain_text_val == concat_string, (plain_text_val, concat_string)
        else:
          unique_match_key_dict[match_key] = concat_string
    
    enc_match_key_dict[tuple(attr_comb)] = attr_comb_match_key_dict
  
  return enc_match_key_dict, unique_match_key_dict

# -----------------------------------------------------------------------------

def create_ind_match_key_dict(data_dict, attr_comb):
    
  attr_comb_match_key_dict = {}
  
  for rec_id, rec_list in data_dict.iteritems():
    
    if(all(rec_list[attr_index] != ' ' and len(rec_list[attr_index]) != 0 for attr_index in attr_comb)):
      
      concat_string = ','.join(rec_list[attr_index] for attr_index in attr_comb)
      
      if(concat_string in attr_comb_match_key_dict):
        rec_id_list = attr_comb_match_key_dict[concat_string]
        rec_id_list.append(rec_id)
        attr_comb_match_key_dict[concat_string] = rec_id_list
      else:
        rec_id_list = [rec_id]
        attr_comb_match_key_dict[concat_string] = rec_id_list
  
  return attr_comb_match_key_dict

# -----------------------------------------------------------------------------

def compute_match_key_freq(enc_match_key_dict):
  
  match_key_freq_dict = {}
  
  for attr_comb, attr_comb_match_key_dict in enc_match_key_dict.iteritems():
    
    sub_freq_dict = {}
    
    for match_key, rec_id_set in attr_comb_match_key_dict.iteritems():
      sub_freq_dict[match_key] = len(rec_id_set)
    
    match_key_freq_dict[attr_comb] = sub_freq_dict
    
  return match_key_freq_dict

# -----------------------------------------------------------------------------

def compute_match_key_freq_solution(enc_match_key_dict):
  
  match_key_freq_dict = {}
  
  for attr_comb, attr_comb_match_key_dict in enc_match_key_dict.iteritems():
    
    sub_freq_dict = {}
    
    for match_key, rec_id_set in attr_comb_match_key_dict.iteritems():
      
      if(len(rec_id_set) > 1):
        continue
      else:
        sub_freq_dict[match_key] = len(rec_id_set)
    
    match_key_freq_dict[attr_comb] = sub_freq_dict
    
  return match_key_freq_dict

# -----------------------------------------------------------------------------

def compute_plain_text_freq(attr_comb_list, plain_data_dict, distr_min_freq):
  
  plain_text_freq_dict = {}
  plain_unique_num_match_key_dict = {}
  
  for rec_id, rec_list in plain_data_dict.iteritems():
    
    for attr_comb in attr_comb_list:
      
      if(all(rec_list[attr_index] != ' ' and len(rec_list[attr_index]) != 0 for attr_index in attr_comb)):
        concat_string = ','.join(rec_list[attr_index] for attr_index in attr_comb)
      
      else:
        #concat_string = 'nokey'
        continue
        
      attr_comb = tuple(attr_comb)
      sub_freq_dict = plain_text_freq_dict.get(attr_comb, {})
      sub_freq_dict[concat_string] = sub_freq_dict.get(concat_string, 0) + 1
      plain_text_freq_dict[attr_comb] = sub_freq_dict
      
  
  # Check if we have attribute combinations with enough frequency distributions
  #
  filtered_plain_freq_dict = {}
  
  for attr_comb in plain_text_freq_dict.keys():
        
    # Get the frequency distribution for the considered plain-text
    # attribute combination and sort the distribution descending order
    plain_sub_freq_dict = plain_text_freq_dict[attr_comb]
    plain_freq_list = sorted([freq for key, freq in 
                              plain_sub_freq_dict.items()],
                              reverse=True)
    
    if(plain_freq_list[0] >= distr_min_freq):
      filtered_plain_freq_dict[attr_comb] = plain_sub_freq_dict
    
    plain_unique_num_match_key_dict[attr_comb] = len(plain_freq_list)
        
    
  return filtered_plain_freq_dict, plain_unique_num_match_key_dict


# -----------------------------------------------------------------------------

def ident_comb_plain_text_id_set(ident_attr_comb_list, plain_data_dict):
  
  plain_text_id_dict = {}
  
  for rec_id, rec_list in plain_data_dict.iteritems():
    
    for attr_comb in ident_attr_comb_list:
      
      if(all(rec_list[attr_index] != ' ' and len(rec_list[attr_index]) != 0 for attr_index in attr_comb)):
        concat_string = ','.join(rec_list[attr_index] for attr_index in attr_comb)
      
      else:
        continue
        
      attr_comb = tuple(attr_comb)
      sub_id_dict = plain_text_id_dict.get(attr_comb, {})
      id_set = sub_id_dict.get(concat_string, set())
      id_set.add(rec_id)
      
      sub_id_dict[concat_string] = id_set
      plain_text_id_dict[attr_comb] = sub_id_dict

  return plain_text_id_dict

# -----------------------------------------------------------------------------

def min_max_normalise(val_list, reverse_flag=False):
  
  normalised_list = []
  
  min_val = min(val_list)
  max_val = max(val_list)
  
  if(min_val == 0.0 and max_val == 0.0):
    normalised_list = val_list
    
  elif(max_val - min_val == 0.0):
    normalised_list = [1.0 for _ in range(len(val_list))]
  
  else:
    for val in val_list:
      new_val = float(val - min_val)/(max_val - min_val)
      
      if(reverse_flag):
        new_val = 1.0 - new_val
        
      normalised_list.append(new_val)
    
  return normalised_list

# -----------------------------------------------------------------------------

def freq_distr_stat_analysis(plain_text_freq_dict, enc_freq_list, true_attr_comb):
  
  # List of all the statistical tests used
  stat_test_list = ['mean', 'std', 'var', 'skew', 'emd', 'hist', 'ksstat', 
                    'entrpy', 'pcstat', 'spstat']
  
  # A list of potential attribute combinations selected by the statistical
  # analysis
  poss_attr_comb_list = []
  
  # Statistical tests results for true attribute combination 
  true_comb_stat_res = []
  
  # For each statistical test store the statistical values obtained by
  # each attribute combination
  stat_test_res_dict = {}
  
  # Dictionary with all the statical resul values for each combination
  stat_res_comb_dict = {}
  
  min_freq_limit = 5
  
  for attr_comb in plain_text_freq_dict.keys():
        
    # Get the frequency distribution for the considered plain-text
    # attribute combination and sort the distribution descending order
    plain_sub_freq_dict = plain_text_freq_dict[attr_comb]
    plain_freq_list = sorted([freq for key, freq in 
                              plain_sub_freq_dict.items()],
                              reverse=True)
    
    plain_freq_list = [freq for freq in plain_freq_list if freq >= min_freq_limit]
    enc_freq_list   = [freq for freq in enc_freq_list if freq >= min_freq_limit]
    
    # Calculate basic statistics of the two distributions and
    # compare them. These include mean, standard deviation,
    # variance, and skewness
    #
    basic_stat_diff_tuple = calc_basic_stat_diff(enc_freq_list, 
                                                 plain_freq_list)
    # Calculate Earth Mover Distance
    emd_val         = earth_mover_distance(enc_freq_list, plain_freq_list)
    
    # Calculate histogram intersection
    hist_interc     = calc_histogram_intersection(enc_freq_list, 
                                                  plain_freq_list)
    
    # Calculate K-S statistics
    ks_stat_res     = stats.ks_2samp(enc_freq_list, plain_freq_list)
    ks_stat         = ks_stat_res[0]
    ks_p_val        = ks_stat_res[1]  
    
    # Calculate entropy value for the encode key distribution
    # based on plain-text value distribution
    entropy_val      = calc_entropy(enc_freq_list, plain_freq_list)
    
    # Calculate pearson and spearman's rank correlation
    # based on two frequency distributions
    if(len(enc_freq_list) > len(plain_freq_list)):
      nw_encode_freq_list = list(numpy.random.choice(enc_freq_list, \
                                                len(plain_freq_list)))
      nw_plain_freq_list = plain_freq_list
      
    elif(len(enc_freq_list) < len(plain_freq_list)):
      nw_plain_freq_list = list(numpy.random.choice(plain_freq_list, \
                                               len(enc_freq_list)))
      nw_encode_freq_list = enc_freq_list
    
    else:
      nw_encode_freq_list = enc_freq_list
      nw_plain_freq_list = plain_freq_list
    
    pc_stat_res = stats.pearsonr(sorted(nw_encode_freq_list), \
                                       sorted(nw_plain_freq_list))
    sc_stat_res = stats.spearmanr(sorted(nw_encode_freq_list), \
                                        sorted(nw_plain_freq_list))
    
    pc_stat  = pc_stat_res[0]
    pc_r_val = pc_stat_res[1]
    
    sc_stat  = sc_stat_res[0]
    sc_r_val = sc_stat_res[1]
    
    # Create a list which contain all calculated statistical values
    stat_res_list = [basic_stat_diff_tuple[0], basic_stat_diff_tuple[1], 
                     basic_stat_diff_tuple[2], basic_stat_diff_tuple[3], 
                     emd_val, hist_interc, ks_stat, entropy_val, pc_stat,
                     sc_stat]
    
    stat_res_comb_dict[attr_comb] = stat_res_list
      
    # For each statistical test create a dictionary with all the attribute
    # combinations and values they got for the test
    for i, stat_test in enumerate(stat_test_list):
      attr_comb_stat_res_dict = stat_test_res_dict.get(stat_test, {})
      attr_comb_stat_res_dict[tuple(attr_comb)] = stat_res_list[i]
      stat_test_res_dict[stat_test] = attr_comb_stat_res_dict
  
  # Loop over each statistical test and find out which attribute 
  # combination got the best value for that test and append those
  # attribute combinations to a list
  for stat_test in stat_test_list:
    attr_comb_res_dict = stat_test_res_dict[stat_test]
    
    if(stat_test in ['mean', 'std', 'var', 'skew', 'emd', 'ksstat', \
                     'entrpy']):
      attr_comb_res_list = sorted(attr_comb_res_dict.items(), 
                                  key=lambda x: x[1], reverse=False)
    else:
      attr_comb_res_list = sorted(attr_comb_res_dict.items(), 
                                  key=lambda x: x[1], reverse=True)
    
    poss_attr_comb_list.append(attr_comb_res_list[0][0])
      
  # By going over the identified attribute combination list find out what
  # attribute combination performed best in most of the statistical tests
  # and select that attribute ombination as the most possible combination
  #
  max_count_attr_comb = set()
  max_count = 0
  
  for attr_comb in poss_attr_comb_list:
    c = poss_attr_comb_list.count(attr_comb)
    
    if(c > max_count):
      max_count = c
      max_count_attr_comb = set([attr_comb])
      
    elif(c == max_count):
      max_count_attr_comb.add(attr_comb)
    
    else:
      continue
  
  # A dictionary with identified attribute combinations and corresponding
  # statistical test values
  ident_attr_comb_dict = {}
  
  for attr_comb in max_count_attr_comb:
    ident_attr_comb_dict[attr_comb] = stat_res_comb_dict[attr_comb]
  
  return ident_attr_comb_dict

# -----------------------------------------------------------------------------

def get_freq_distr_stat_res(plain_text_freq_dict, enc_freq_list, true_attr_comb):
  
  # Dictionary with all the statical resul values for each combination
  stat_res_comb_dict = {}
  
  min_freq_limit = 1
  
  # first filtering step using frequency tolerance parameter epsilon
  num_top_freq_val_consdr = 5
  freq_tolerance_param_dict = {'<10': 0.9, '<20': 0.7, '<100': 0.5, '<1000': 0.3, '<5000': 0.2, '>5000': 0.1}
  num_out_range_attr_comb_list = []
  
  
  for attr_comb in plain_text_freq_dict.keys():
        
    # Get the frequency distribution for the considered plain-text
    # attribute combination and sort the distribution descending order
    plain_sub_freq_dict = plain_text_freq_dict[attr_comb]
    plain_freq_list = sorted([freq for key, freq in 
                              plain_sub_freq_dict.items()],
                              reverse=True)
    
    plain_freq_list = [freq for freq in plain_freq_list if freq >= min_freq_limit]
    enc_freq_list   = [freq for freq in enc_freq_list if freq >= min_freq_limit]
    top_enc_freq_val = enc_freq_list[0]
    
    if(len(plain_freq_list) < 10 or len(enc_freq_list) < 10):
      # frequency lists do not have enough values to conduct frequency analysis
      continue
    
    if(top_enc_freq_val < 10):
      freq_tolerance_ratio = freq_tolerance_param_dict['<10']
    elif(top_enc_freq_val < 20):
      freq_tolerance_ratio = freq_tolerance_param_dict['<20']
    elif(top_enc_freq_val < 100):
      freq_tolerance_ratio = freq_tolerance_param_dict['<100']
    elif(top_enc_freq_val < 1000):
      freq_tolerance_ratio = freq_tolerance_param_dict['<1000']
    elif(top_enc_freq_val < 5000):
      freq_tolerance_ratio = freq_tolerance_param_dict['<5000']
    else:
      freq_tolerance = freq_tolerance_param_dict['>5000']
    
    num_out_range_val = 0
    freq_tolerance = top_enc_freq_val*freq_tolerance_ratio
    
    for i,enc_freq_val in enumerate(enc_freq_list[:num_top_freq_val_consdr]):
      
      plain_freq_val = plain_freq_list[i]
      
      if(plain_freq_val < (enc_freq_val - freq_tolerance) or plain_freq_val > (enc_freq_val + freq_tolerance)):
        num_out_range_val += 1
    
    if(num_out_range_val >= 3):
      num_out_range_attr_comb_list.append(attr_comb)
      continue 
      
    if(len(plain_freq_list) == 0 or len(enc_freq_list) == 0):
      continue
    
    # Calculate basic statistics of the two distributions and
    # compare them. These include mean, standard deviation,
    # variance, and skewness
    #
    basic_stat_diff_tuple = calc_basic_stat_diff(enc_freq_list, 
                                                 plain_freq_list)
    # Calculate Earth Mover Distance
    emd_val         = earth_mover_distance(enc_freq_list, plain_freq_list)
    
    # Calculate histogram intersection
    hist_interc     = calc_histogram_intersection(enc_freq_list, 
                                                  plain_freq_list)
    
    # Calculate K-S statistics
    ks_stat_res     = stats.ks_2samp(enc_freq_list, plain_freq_list)
    ks_stat         = ks_stat_res[0]
    ks_p_val        = ks_stat_res[1]  
    
    # Calculate entropy value for the encode key distribution
    # based on plain-text value distribution
    entropy_val      = calc_entropy(enc_freq_list, plain_freq_list)
    
    # Calculate pearson and spearman's rank correlation
    # based on two frequency distributions
    if(len(enc_freq_list) > len(plain_freq_list)):
      nw_encode_freq_list = list(numpy.random.choice(enc_freq_list, \
                                                len(plain_freq_list)))
      nw_plain_freq_list = plain_freq_list
      
    elif(len(enc_freq_list) < len(plain_freq_list)):
      nw_plain_freq_list = list(numpy.random.choice(plain_freq_list, \
                                               len(enc_freq_list)))
      nw_encode_freq_list = enc_freq_list
    
    else:
      nw_encode_freq_list = enc_freq_list
      nw_plain_freq_list = plain_freq_list
    
    pc_stat_res = stats.pearsonr(sorted(nw_encode_freq_list), \
                                       sorted(nw_plain_freq_list))
    sc_stat_res = stats.spearmanr(sorted(nw_encode_freq_list), \
                                        sorted(nw_plain_freq_list))
    
    pc_stat  = pc_stat_res[0]
    pc_r_val = pc_stat_res[1]
    
    sc_stat  = sc_stat_res[0]
    sc_r_val = sc_stat_res[1]
    
    
    if(math.isnan(pc_stat)):
      pc_stat = 0.0
      
    if(math.isnan(sc_stat)):
      sc_stat = 0.0
    
    # Create a list which contain all calculated statistical values
    stat_res_list = [basic_stat_diff_tuple[0], basic_stat_diff_tuple[1], 
                     basic_stat_diff_tuple[2], basic_stat_diff_tuple[3], 
                     emd_val, hist_interc, ks_stat, entropy_val, pc_stat,
                     sc_stat]
    
    stat_res_comb_dict[attr_comb] = stat_res_list
    
  print '   ### Plain-text combinations that were out of the range:', num_out_range_attr_comb_list
  print '   ### Total number of combinations found:', len(num_out_range_attr_comb_list)
  print
  
  return stat_res_comb_dict

# -----------------------------------------------------------------------------

def match_key_record_linkage1(enc_match_key_dict, plain_match_key_dict, sample_size=None):
  
  
  if(sample_size != None):
    random.seed(random.randint(0, sys.maxint))
    
    full_enc_id_set = set(enc_match_key_dict.keys())
    full_plain_id_set = set(plain_match_key_dict.keys())
    
    enc_id_set   = set(random.sample(full_enc_id_set, sample_size))
    plain_id_set = set(random.sample(full_plain_id_set, sample_size))
    
  else:
    enc_id_set = set(enc_match_key_dict.keys())
    plain_id_set = set(plain_match_key_dict.keys())
    
  true_match_rec_id = enc_id_set.intersection(plain_id_set)
  
  ident_match_rec_pairs = []
  corr_num_rec_pairs = 0
  
  for enc_id in enc_id_set:
    
    enc_key_list = enc_match_key_dict[enc_id]
    
    for plain_id in plain_id_set:
      
      plain_key_list = plain_match_key_dict[plain_id]
      
      if(any(key in plain_key_list for key in enc_key_list)):
        
        ident_match_rec_pairs.append((enc_id,plain_id))
        
        if(plain_id == enc_id):
          corr_num_rec_pairs += 1
          
  prec_val  = float(corr_num_rec_pairs)/len(ident_match_rec_pairs)
  rec_val   = float(corr_num_rec_pairs)/len(true_match_rec_id)
  f_measure = 2*(prec_val*rec_val)/(prec_val + rec_val)
  
  return ident_match_rec_pairs, prec_val, rec_val, f_measure

# -----------------------------------------------------------------------------

def match_key_record_linkage_n(enc_data_dict, plain_data_dict, 
                               attr_comb_list, num_true_matches):
  
  ident_match_rec_pairs = set()
  
  num_tp = 0
  num_fp = 0
  num_fn = 0
  num_tn = 0
  
  true_pos_ids = set()
  false_pos_id_pairs = set()
  
  sorted_attr_comb_list = sorted(attr_comb_list, key=lambda x: len(x), reverse=True)
  
  for attr_comb in sorted_attr_comb_list:
    
    enc_comb_match_key_dict = create_ind_match_key_dict(enc_data_dict, attr_comb)
    plain_comb_match_key_dict = create_ind_match_key_dict(plain_data_dict, attr_comb)
    
    for concat_string in enc_comb_match_key_dict.keys():
      
      if(concat_string in plain_comb_match_key_dict):
        
        enc_rec_id_list   = enc_comb_match_key_dict[concat_string]
        plain_rec_id_list = plain_comb_match_key_dict[concat_string]
        
        all_poss_pairs = itertools.product(enc_rec_id_list, plain_rec_id_list)
        
        for rec_id_pair in all_poss_pairs:
          enc_id = rec_id_pair[0]
          plain_id = rec_id_pair[1]
          
          #ident_match_rec_pairs.add(rec_id_pair)
          
          if(enc_id == plain_id):
            true_pos_ids.add(enc_id)
          else:
            false_pos_id_pairs.add((enc_id,plain_id))
      
    del enc_comb_match_key_dict
    del plain_comb_match_key_dict
  
  num_tp = len(true_pos_ids)
  num_fp = len(false_pos_id_pairs)
  num_fn = num_true_matches - num_tp
  
  del true_pos_ids
  del false_pos_id_pairs
  
  # Calculating precision
  if(num_tp + num_fp > 0):
    prec_val  = float(num_tp)/(num_tp + num_fp)
  else:
    prec_val = 0.0
  
  # Calculating recall  
  if(num_tp + num_fn > 0):
    reca_val  = float(num_tp)/(num_tp + num_fn)
  else:
    reca_val = 0.0
  
  # Calculating f-measure
  if(prec_val + reca_val > 0):
    f_measure = 2*(prec_val*reca_val)/(prec_val + reca_val)
  else:
    f_measure = 0.0
  
  return ident_match_rec_pairs, prec_val, reca_val, f_measure, \
    num_tp, num_fp, num_tn, num_fn

# -----------------------------------------------------------------------------

def record_linkage_with_missing(enc_data_dict, plain_data_dict, 
                               attr_comb_list, num_true_matches):
  
  ident_match_rec_pairs = set()
  
  num_tp = 0
  num_fp = 0
  num_fn = 0
  num_tn = 0
  
  true_pos_ids = set()
  false_pos_id_pairs = set()
  
  sorted_attr_comb_list = sorted(attr_comb_list, key=lambda x: len(x), reverse=True)
  
  for attr_comb in sorted_attr_comb_list:
    
    enc_comb_match_key_dict = create_ind_match_key_dict(enc_data_dict, attr_comb)
    plain_comb_match_key_dict = create_ind_match_key_dict(plain_data_dict, attr_comb)
    
    for concat_string in enc_comb_match_key_dict.keys():
      
      if(concat_string in plain_comb_match_key_dict):
        
        enc_rec_id_list   = enc_comb_match_key_dict[concat_string]
        plain_rec_id_list = plain_comb_match_key_dict[concat_string]
        
        if(len(enc_rec_id_list) > 1 or len(plain_rec_id_list) > 1):
          # Do not consider these records since they have frequency above 1
          continue
        
        assert len(enc_rec_id_list) == len(plain_rec_id_list) == 1
        
        enc_id = enc_rec_id_list[0]
        plain_id = plain_rec_id_list[0]
        
        if(enc_id == plain_id):
          true_pos_ids.add(enc_id)
        else:
          false_pos_id_pairs.add((enc_id,plain_id))
      
    del enc_comb_match_key_dict
    del plain_comb_match_key_dict
  
  num_tp = len(true_pos_ids)
  num_fp = len(false_pos_id_pairs)
  num_fn = num_true_matches - num_tp
  
  del true_pos_ids
  del false_pos_id_pairs
  
  # Calculating precision
  if(num_tp + num_fp > 0):
    prec_val  = float(num_tp)/(num_tp + num_fp)
  else:
    prec_val = 0.0
  
  # Calculating recall  
  if(num_tp + num_fn > 0):
    reca_val  = float(num_tp)/(num_tp + num_fn)
  else:
    reca_val = 0.0
  
  # Calculating f-measure
  if(prec_val + reca_val > 0):
    f_measure = 2*(prec_val*reca_val)/(prec_val + reca_val)
  else:
    f_measure = 0.0
  
  return ident_match_rec_pairs, prec_val, reca_val, f_measure, \
    num_tp, num_fp, num_tn, num_fn

# -----------------------------------------------------------------------------


def match_key_record_linkage(enc_match_key_dict, plain_match_key_dict, 
                             num_true_matches):
  
  ident_match_rec_pairs = set()
  
  num_tp = 0
  num_fp = 0
  num_fn = 0
  num_tn = 0
  
  true_pos_ids = set()
  false_pos_id_pairs = set()
  
  for attr_comb_tuple in enc_match_key_dict.keys():
    
    enc_comb_match_key_dict = enc_match_key_dict[attr_comb_tuple]
    plain_comb_match_key_dict = plain_match_key_dict[attr_comb_tuple]
    
    for concat_string in enc_comb_match_key_dict.keys():
      
      if(concat_string in plain_comb_match_key_dict):
        
        enc_rec_id_list   = enc_comb_match_key_dict[concat_string]
        plain_rec_id_list = plain_comb_match_key_dict[concat_string]
        
        all_poss_pairs = itertools.product(enc_rec_id_list, plain_rec_id_list)
        
        for rec_id_pair in all_poss_pairs:
          enc_id = rec_id_pair[0]
          plain_id = rec_id_pair[1]
          
          ident_match_rec_pairs.add(rec_id_pair)
          
          if(enc_id == plain_id):
            true_pos_ids.add(enc_id)
          else:
            false_pos_id_pairs.add((enc_id,plain_id))
  
  num_tp = len(true_pos_ids)
  num_fp = len(false_pos_id_pairs)
  num_fn = num_true_matches - num_tp
  
  # Calculating precision
  if(num_tp + num_fp > 0):
    prec_val  = float(num_tp)/(num_tp + num_fp)
  else:
    prec_val = 0.0
  
  # Calculating recall  
  if(num_tp + num_fn > 0):
    reca_val  = float(num_tp)/(num_tp + num_fn)
  else:
    reca_val = 0.0
  
  # Calculating f-measure
  if(prec_val + reca_val > 0):
    f_measure = 2*(prec_val*reca_val)/(prec_val + reca_val)
  else:
    f_measure = 0.0
  
  return ident_match_rec_pairs, prec_val, reca_val, f_measure, \
    num_tp, num_fp, num_tn, num_fn

# -----------------------------------------------------------------------------

def single_match_key_record_linkage(enc_data_dict, plain_data_dict, attr_num_list,
                                    num_true_matches):
  
  ident_match_rec_pairs = []
  
  num_tp = 0
  num_fp = 0
  num_fn = 0
  num_tn = 0
  
  true_pos_ids = set()
  false_pos_id_pairs = set()
    
  enc_comb_match_key_dict = create_ind_match_key_dict(enc_data_dict, attr_num_list)
  plain_comb_match_key_dict = create_ind_match_key_dict(plain_data_dict, attr_num_list)
  
  for concat_string in enc_comb_match_key_dict.keys():
    
    if(concat_string in plain_comb_match_key_dict):
      
      enc_rec_id_list   = enc_comb_match_key_dict[concat_string]
      plain_rec_id_list = plain_comb_match_key_dict[concat_string]
      
      all_poss_pairs = itertools.product(enc_rec_id_list, plain_rec_id_list)
      
      for rec_id_pair in all_poss_pairs:
        enc_id = rec_id_pair[0]
        plain_id = rec_id_pair[1]
        
        if(enc_id == plain_id):
          true_pos_ids.add(enc_id)
        else:
          false_pos_id_pairs.add((enc_id,plain_id))
      
  del enc_comb_match_key_dict
  del plain_comb_match_key_dict
  
  num_tp = len(true_pos_ids)
  num_fp = len(false_pos_id_pairs)
  num_fn = num_true_matches - num_tp
  
  del true_pos_ids
  del false_pos_id_pairs
  
  # Calculating precision
  if(num_tp + num_fp > 0):
    prec_val  = float(num_tp)/(num_tp + num_fp)
  else:
    prec_val = 0.0
  
  # Calculating recall  
  if(num_tp + num_fn > 0):
    reca_val  = float(num_tp)/(num_tp + num_fn)
  else:
    reca_val = 0.0
  
  # Calculating f-measure
  if(prec_val + reca_val > 0):
    f_measure = 2*(prec_val*reca_val)/(prec_val + reca_val)
  else:
    f_measure = 0.0
  
  return ident_match_rec_pairs, prec_val, reca_val, f_measure, \
          num_tp, num_fp, num_tn, num_fn

# -----------------------------------------------------------------------------

def earth_mover_distance(enc_key_freq_dist, plain_key_freq_dist):
  
  try:  # If not implemented will crash
    emd_stat_res = stats.wasserstein_distance(enc_key_freq_dist, \
                                              plain_key_freq_dist)
    
  except:
    emd_stat_res = 99.0
  
  return emd_stat_res

# -----------------------------------------------------------------------------

def get_basic_stat(data_freq_dist):
  
  data_mean   = numpy.mean(data_freq_dist)
  data_median = numpy.median(data_freq_dist)
  data_q1     = numpy.percentile(data_freq_dist, 25)
  data_q3     = numpy.percentile(data_freq_dist, 75)
  data_std    = numpy.std(data_freq_dist)
  data_var    = numpy.var(data_freq_dist)
  
  return data_mean, data_median, data_q1, data_q3, data_std, data_var
  
# -----------------------------------------------------------------------------

def calc_basic_stat_diff(enc_key_freq_dist, plain_key_freq_dist):
  
  enc_key_freq_dist = [freq for freq in enc_key_freq_dist if freq > 1]
  plain_key_freq_dist = [freq for freq in plain_key_freq_dist if freq > 1]
  
  enc_data_mean   = numpy.mean(enc_key_freq_dist)
  #enc_data_median = numpy.median(enc_key_freq_dist)
  #enc_data_q1     = numpy.percentile(enc_key_freq_dist, 25)
  #enc_data_q3     = numpy.percentile(enc_key_freq_dist, 75)
  enc_data_std    = numpy.std(enc_key_freq_dist)
  enc_data_var    = numpy.var(enc_key_freq_dist)
  enc_data_skew   = stats.skew(enc_key_freq_dist)
  
  plain_data_mean   = numpy.mean(plain_key_freq_dist)
  #plain_data_median = numpy.median(plain_key_freq_dist)
  #plain_data_q1     = numpy.percentile(plain_key_freq_dist, 25)
  #plain_data_q3     = numpy.percentile(plain_key_freq_dist, 75)
  plain_data_std    = numpy.std(plain_key_freq_dist)
  plain_data_var    = numpy.var(plain_key_freq_dist)
  plain_data_skew   = stats.skew(plain_key_freq_dist)
  
  if(enc_data_mean + plain_data_mean == 0.0):
    mean_diff = 1.0
  else:
    mean_diff = abs(enc_data_mean - plain_data_mean)/numpy.mean([enc_data_mean, plain_data_mean])
  #median_diff = abs(enc_data_median - plain_data_median)/numpy.mean([enc_data_median, plain_data_median])
  #q1_diff =     abs(enc_data_q1 - plain_data_q1)/numpy.mean([enc_data_q1, plain_data_q1])
  #q3_diff =     abs(enc_data_q3 - plain_data_q3)/numpy.mean([enc_data_q3, plain_data_q3])
  if(enc_data_std + plain_data_std == 0.0):
    std_diff = 1.0
  else:
    std_diff = abs(enc_data_std - plain_data_std)/numpy.mean([enc_data_std, plain_data_std])
  
  if(enc_data_var + plain_data_var == 0.0):
    var_diff = 1.0
  else:
    var_diff = abs(enc_data_var - plain_data_var)/numpy.mean([enc_data_var, plain_data_var])
  
  if(enc_data_skew + plain_data_skew == 0.0):
    skew_diff = 1.0
  else:
    skew_diff = abs(enc_data_skew - plain_data_skew)/numpy.mean([enc_data_skew, plain_data_skew])
  
  #total_diff_perc = numpy.mean([mean_diff, median_diff, q1_diff, q3_diff, std_diff, var_diff])
  
  #total_diff_perc = numpy.mean([skew_diff, std_diff, var_diff])

  return mean_diff, std_diff, var_diff, skew_diff

# -----------------------------------------------------------------------------

def calc_histogram_intersection(enc_key_freq_dist, plain_key_freq_dist):
  
  binning_flag = True
  
  if(binning_flag):
    
    num_bins = 700000
    enc_freq_list = equal_depth_binning(enc_key_freq_dist, num_bins)
    plain_freq_list = equal_depth_binning(plain_key_freq_dist, num_bins) 
    
    hist_dist = 0.0
    
    for i in range(num_bins):
    
      hist_dist += min(enc_freq_list[i], plain_freq_list[i])
    
    avrg_sum = float(sum(enc_freq_list) + sum(plain_freq_list))/2
    
    hist_dist = float(hist_dist)/avrg_sum
    
  else:
  
    if(len(enc_key_freq_dist) > len(plain_key_freq_dist)):
      array_len = len(plain_key_freq_dist)
    else:
      array_len = len(enc_key_freq_dist)
    
    hist_dist = 0.0
    
    for i in range (array_len):
      
      hist_dist += min(enc_key_freq_dist[i], plain_key_freq_dist[i])
    
    avrg_sum = float(sum(plain_key_freq_dist) + sum(enc_key_freq_dist))/2
    
    hist_dist = float(hist_dist)/avrg_sum
  
  return hist_dist

# -----------------------------------------------------------------------------

def calc_entropy(enc_key_freq_dist, plain_key_freq_dist):
  
  trim_enc_freq_list = []
  trim_plain_freq_list = []
  
  i = 0
  j = 0
  
  for val in enc_key_freq_dist:
    if(val > 1):
      trim_enc_freq_list.append(val)
    elif(val == 1 and i == 0):
      trim_enc_freq_list.append(val)
      i += 1
    else:
      continue
  
  for val in plain_key_freq_dist:
    if(val > 1):
      trim_plain_freq_list.append(val)
    elif(val == 1 and j == 0):
      trim_plain_freq_list.append(val)
      j += 1
    else:
      continue
  
  min_len = min(len(trim_enc_freq_list), len(trim_plain_freq_list))
  
  entropy_val = stats.entropy(trim_enc_freq_list[:min_len], trim_plain_freq_list[:min_len])
  
  return entropy_val

# -----------------------------------------------------------------------------

def chi_square_test(ob_data, ex_data):
  
  if(len(ob_data) > len(ex_data)):
    data_len = len(ex_data)
  else:
    data_len = len(ob_data)
  
  stat_res = 0.0
  
  for i in xrange(data_len):
    ob_val = ob_data[i]
    ex_val = ex_data[i]
    
    if(ex_val > 0):
      stat_res += float((ob_val - ex_val)**2)/ex_val
    else:
      continue
  
  return stat_res

# -----------------------------------------------------------------------------
  
def equal_distace_binning(freq_val_list, num_bins=10):
  
  min_val = min(freq_val_list)
  max_val = max(freq_val_list)
  
  bin_range = float(max_val - min_val)/num_bins
  
  bin_val_dict = {}
  
  list_start_point = 0
  
  num_val_added = 0
  
  for i in range(1, num_bins+1):
    
    bin_min = max_val - (bin_range*i)
    bin_max = max_val - (bin_range*(i-1))
    
    bin_val_list = []
    
    for freq_val in freq_val_list[list_start_point:]:
      
      if(i == 1):
        if(freq_val >= bin_min):
          bin_val_list.append(freq_val)
          list_start_point += 1
        else:
          continue
      else:
        if(freq_val >= bin_min and freq_val < bin_max):
          bin_val_list.append(freq_val)
          list_start_point += 1
        else:
          continue
    
    bin_val_dict[i] = bin_val_list
    num_val_added += len(bin_val_list)
  
  assert num_val_added == len(freq_val_list), (num_val_added, len(freq_val_list))
  
  binned_val_list = [numpy.mean(bin_val_dict[bin]) for bin in range(1, num_bins+1)]
        
  return binned_val_list

# -----------------------------------------------------------------------------
  
def equal_depth_binning(freq_val_list, num_bins=1000):
  
  bin_freq = int(float(len(freq_val_list))/num_bins)
  
  bin_val_dict = {}
  
  for i in range(1, num_bins+1):

    if(i == num_bins):
      bin_val_list = freq_val_list[bin_freq*(i-1):]
    else:
      bin_val_list = freq_val_list[bin_freq*(i-1):bin_freq*i]
    
    bin_val_dict[i] = bin_val_list
  
  binned_val_list = [numpy.mean(bin_val_dict[bin]) for bin in range(1, num_bins+1)]
        
  return binned_val_list

# -----------------------------------------------------------------------------

def rule_based_check(num_matched_basic_stat, num_matched_adv_stat):
  
  matched_flag = False
  
  if(num_matched_adv_stat == 3):
    matched_flag = True
   
  if(num_matched_adv_stat >= 1 and num_matched_basic_stat == 4):
    matched_flag = True
   
  if(num_matched_adv_stat >= 3 and num_matched_basic_stat >= 2):
    matched_flag = True
   
  if(num_matched_adv_stat >= 2 and num_matched_basic_stat >= 4):
    matched_flag = True
    
  #if(num_matched_adv_stat >= 3):
    #matched_flag = True
  
  return matched_flag

# -----------------------------------------------------------------------------

def check_perfct_alignment(poss_comb_dict):
  
  perfct_alignmnt_res_list = [0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0]
  
  new_comb_dict = {}
  
  for poss_comb, stat_list in poss_comb_dict.iteritems():
    
    basic_stat_num_align = 0
    adv_stat_num_align   = 0
    
    for i, stat_res in enumerate(stat_list):
      
      if(stat_res == perfct_alignmnt_res_list[i]):
        
        if(i < 5):
          basic_stat_num_align += 1
        else:
          adv_stat_num_align += 1
      
    if(adv_stat_num_align == 5):
      new_comb_dict[poss_comb] = stat_list
    elif(adv_stat_num_align + basic_stat_num_align >= 7):
      new_comb_dict[poss_comb] = stat_list
  
  return new_comb_dict

# -----------------------------------------------------------------------------

def check_stat_res_diff(poss_comb_dict):
  
  new_comb_dict = {}
  
  stat_test_res_dict = {}
  
  # List of all the statistical tests used
  stat_test_list = ['mean', 'std', 'var', 'skew', 'emd', 'hist', 'ksstat', 
                    'ksp', 'entrpy']
  
  for poss_comb, stat_res_list in poss_comb_dict.iteritems():
  
    # For each statistical test create a dictionary with all the attribute
    # combinations and values they got for the test
    for i, stat_test in enumerate(stat_test_list):
      attr_comb_stat_res_dict = stat_test_res_dict.get(stat_test, {})
      attr_comb_stat_res_dict[poss_comb] = stat_res_list[i]
      stat_test_res_dict[stat_test] = attr_comb_stat_res_dict
    
  ident_comb_list = []
  
  for stat_test in stat_test_list:
    attr_comb_res_dict = stat_test_res_dict[stat_test]
    
    if(stat_test in ['mean', 'std', 'var', 'skew']):
      continue
    
    if(stat_test in ['emd', 'ksstat', 'entrpy']):
      attr_comb_res_list = sorted(attr_comb_res_dict.items(), 
                                  key=lambda x: x[1], reverse=False)
    else:
      attr_comb_res_list = sorted(attr_comb_res_dict.items(), 
                                  key=lambda x: x[1], reverse=True)
    
    i = 0
    #j = 1
    
    ident_comb_set = set()
    
    while((i+1)<len(attr_comb_res_list)):
      
      stat_res_tuple_1 = attr_comb_res_list[i]
      stat_res_tuple_2 = attr_comb_res_list[i+1]
      
      stat_res_1 = stat_res_tuple_1[1]
      stat_res_2 = stat_res_tuple_2[1]
      
      stat_res_diff = float(abs(stat_res_1 - stat_res_2))/numpy.mean([stat_res_1,stat_res_2])
      
      if(stat_res_diff < 0.07):
        ident_comb_set.add(stat_res_tuple_1[0])
        ident_comb_set.add(stat_res_tuple_2[0])
      else:
        ident_comb_set.add(stat_res_tuple_1[0])
        break
      
      i += 1
      #j += 1
    
    for ident_comb in ident_comb_set:
      ident_comb_list.append(ident_comb)
    
  max_count_attr_comb = set()
  max_count = 0
  
  for attr_comb in ident_comb_list:
    c = ident_comb_list.count(attr_comb)
    
    if(c > max_count):
      max_count = c
      max_count_attr_comb = set([attr_comb])
      
    elif(c == max_count):
      max_count_attr_comb.add(attr_comb)
    
    else:
      continue
  
  for attr_comb in max_count_attr_comb:
    new_comb_dict[attr_comb] = poss_comb_dict[attr_comb]
  
  return new_comb_dict

# -----------------------------------------------------------------------------

def check_supersets(poss_comb_dict, ident_comb_list):
  
  new_comb_dict = {}
  
  if(len(ident_comb_list) > 0):
    
    for poss_comb, stat_res_list in poss_comb_dict.iteritems():
      
      poss_comb_set = set(poss_comb)
      
      superset_subset_flag = False
      
      for ident_comb in ident_comb_list:
        
        ident_comb_set = set(ident_comb)
        
        if(ident_comb_set.issubset(poss_comb_set) or ident_comb_set.issuperset(poss_comb_set)):
          superset_subset_flag = True
        
      if(superset_subset_flag == False):
        new_comb_dict[poss_comb] = stat_res_list
  
  return new_comb_dict 

# -----------------------------------------------------------------------------

def evaluate_attack_res(identified_val_dict):
  
  # Calculate precision and recall
  #
  main_prec_list = []
  main_rec_list = []
  
  exact_corr_ids = set()
  part_corr_ids  = set()
  wrng_ids       = set()
  
  ident_attr_val_dict = {}
  
  for attr_comb_tuple, ident_plain_val_dict in identified_val_dict.iteritems():

    true_attr_comb = attr_comb_tuple[0]
    guessed_attr_comb = attr_comb_tuple[1]
    
    prec_list = []
    rec_list = []
    
    for freq_tuple in ident_plain_val_dict.keys():
      
      true_val_set    = ident_plain_val_dict[freq_tuple][0]
      guessed_val_set = ident_plain_val_dict[freq_tuple][1]
      guessed_id_set  = ident_plain_val_dict[freq_tuple][2]
    
      if(len(guessed_val_set) == 0 or len(true_val_set) == 0):
        continue
    
      corr_val_set = true_val_set.intersection(guessed_val_set)
      
      for plain_id in guessed_id_set:
        ident_val_set_pair = ident_attr_val_dict.get(plain_id, [set(), set()])
        
        ident_corr_val_set = ident_val_set_pair[0]
        ident_wrng_val_set = ident_val_set_pair[1]
        
        ident_corr_val_set.update(corr_val_set)
        ident_wrng_val_set.update(guessed_val_set - corr_val_set)
        
        ident_attr_val_dict[plain_id] = [ident_corr_val_set, ident_wrng_val_set]
      
      if(len(corr_val_set) == len(guessed_val_set)):
        exact_corr_ids.update(guessed_id_set)
      elif(len(corr_val_set) == 0):
        wrng_ids.update(guessed_id_set)
      else:
        part_corr_ids.update(guessed_id_set)
      
      prec_val = float(len(corr_val_set))/len(guessed_val_set)
      rec_val  = float(len(corr_val_set))/len(true_val_set)
      
      if(math.isnan(prec_val) == False):
        prec_list.append(prec_val)
      
      if(math.isnan(rec_val) == False):
        rec_list.append(rec_val)
    
    if(len(prec_list) > 0):
      main_prec_list.append(numpy.mean(prec_list))
    
    if(len(rec_list) > 0):
      main_rec_list.append(numpy.mean(rec_list))
  
  return main_prec_list, main_rec_list, ident_attr_val_dict, \
    exact_corr_ids, part_corr_ids, wrng_ids

# -----------------------------------------------------------------------------

def print_num_match_key_diff_freq(match_key_freq_dict):
  
  attr_index_set = set()
  
  for attr_comb in match_key_freq_dict.keys():
    
    for attr_index in attr_comb:
      attr_index_set.add((enc_header_list[attr_index], attr_index))
    
    sub_freq_dict = match_key_freq_dict[attr_comb]
    
    num_uniqe_match_keys = len(sub_freq_dict)
    
    freq_list = sorted(sub_freq_dict.values(), reverse=True)
    
    more_1_freq_list = [freq for freq in freq_list if freq > 1]
    
    num_match_keys_freq_above_1 = len(more_1_freq_list)
    num_rec_freq_above_1 = sum(more_1_freq_list)
    
    print 'Attribute combination:', attr_comb
    print '  Number of unique match-keys:            ', num_uniqe_match_keys
    print '  Number of match-keys with frequency > 1:', num_match_keys_freq_above_1
    print '  Number of records with frequency > 1:   ', num_rec_freq_above_1
    print '  Top 5 frequencies of match-keys:        ', more_1_freq_list[:5]
    print
  
  return attr_index_set

#=============================================================================
# Main program
#===============================================================================

encode_data_set_name =    sys.argv[1]
encode_rec_id_col =       int(sys.argv[2])
encode_col_sep_char =     sys.argv[3]
encode_header_line_flag = eval(sys.argv[4])
#
plain_data_set_name =     sys.argv[5]
plain_rec_id_col =        int(sys.argv[6])
plain_col_sep_char =      sys.argv[7]
plain_header_line_flag =  eval(sys.argv[8])
#
sample_size =             int(sys.argv[9])
run_method =              sys.argv[10]

if(run_method == 'attack'):
  min_weight_score =        float(sys.argv[11])
  attacker_knwlge =         sys.argv[12]
  attack_step =             sys.argv[13]
  consdrd_top_num_val =     int(sys.argv[14]) # only if you are measuring precision at k
  
  assert attacker_knwlge in ['comb', 'attr', 'dom'], attacker_knwlge
  assert attack_step in ['main', 're-ident'], attack_step
#
#
assert encode_rec_id_col >= 0, encode_rec_id_col
assert encode_header_line_flag in [True, False], encode_header_line_flag
#
assert run_method in ['attack', 'linkage'], run_method
#
assert sample_size <= 100 and sample_size > 0, sample_size

if (len(encode_col_sep_char) > 1):
  if (encode_col_sep_char == 'tab'):
    encode_col_sep_char = '\t'
  elif (encode_col_sep_char[0] == '"') and (encode_col_sep_char[-1] == '"') \
       and (len(encode_col_sep_char) == 3):
    encode_col_sep_char = encode_col_sep_char[1]
  else:
    print 'Illegal encode data set column separator format:', \
          encode_col_sep_char

if (len(plain_col_sep_char) > 1):
  if (plain_col_sep_char == 'tab'):
    plain_col_sep_char = '\t'
  elif (plain_col_sep_char[0] == '"') and \
     (plain_col_sep_char[-1] == '"') and \
     (len(plain_col_sep_char) == 3):
    plain_col_sep_char = plain_col_sep_char[1]
  else:
    print 'Illegal plain text data set column separator format:', \
          plain_col_sep_char

# Check if same data sets and same attributes were given
#
if ((encode_data_set_name == plain_data_set_name) and \
    (encode_attr_list == plain_attr_list)):
  same_data_attr_flag = True
else:
  same_data_attr_flag = False

# Get base names of data sets (remove directory names) for summary output
#
encode_base_data_set_name = encode_data_set_name.split('/')[-1]
encode_base_data_set_name = encode_base_data_set_name.replace('.csv', '')
encode_base_data_set_name = encode_base_data_set_name.replace('.gz', '')
assert ',' not in encode_base_data_set_name

plain_base_data_set_name = plain_data_set_name.split('/')[-1]
plain_base_data_set_name = plain_base_data_set_name.replace('.csv', '')
plain_base_data_set_name = plain_base_data_set_name.replace('.gz', '')
assert ',' not in plain_base_data_set_name

res_file_name = 'pprl-attack-match-keys-results-%s-%s-%s.csv' % \
                (encode_base_data_set_name, plain_base_data_set_name, \
                 today_str)
print
print 'Write results into file:', res_file_name
print
print '-'*80
print

# Check which dataset is used for the experiment
#
if('ncvoter' in encode_base_data_set_name):
  if('balanced' in encode_base_data_set_name):
    dataset_name_str = 'NCVR_BAL'
  elif('500000' in encode_base_data_set_name):
    dataset_name_str = 'NCVR_50'
  else:
    dataset_name_str = 'NCVR_FULL'
elif('foia' in encode_base_data_set_name):
  dataset_name_str = 'MVR_FULL'
else:
  raise Exception, 'Wrong dataset'

attack_attr_list = ATTR_SELECT_DICT[dataset_name_str]['ATTCK_ATTR_LIST']

# Load and exract records from csv databases to dictionaries
#
enc_data_res_tuple = load_data_set_extract_attr_val(encode_data_set_name, 
                                                    encode_rec_id_col, 
                                                    encode_col_sep_char, 
                                                    encode_header_line_flag,
                                                    attack_attr_list,
                                                    sample_size)
                                  
enc_data_dict         = enc_data_res_tuple[0]
enc_header_list       = enc_data_res_tuple[1]
enc_missing_perc_list = enc_data_res_tuple[2]
enc_unique_val_dict   = enc_data_res_tuple[3]
                                 
plain_data_res_tuple = load_data_set_extract_attr_val(plain_data_set_name, 
                                                      plain_rec_id_col, 
                                                      plain_col_sep_char, 
                                                      plain_header_line_flag,
                                                      attack_attr_list,
                                                      sample_size)

plain_data_dict         = plain_data_res_tuple[0]
plain_header_list       = plain_data_res_tuple[1]
plain_missing_perc_list = plain_data_res_tuple[2]
plain_unique_val_dict   = plain_data_res_tuple[3]

# Get the overlap of the datasets
#
enc_rec_id_set   = set(enc_data_dict.keys())
plain_rec_id_set = set(plain_data_dict.keys())

true_match_id_set = enc_rec_id_set.intersection(plain_rec_id_set)

# Do attribute blocking based on selected list of attributes
#
attr_blck_flag = False

if(attr_blck_flag):

  blk_attr_list  = ATTR_SELECT_DICT[dataset_name_str]['BLK_ATTR_LIST']
  
  #enc_blk_dict   = attr_blocking(enc_data_dict, blk_attr_list)
  #plain_blk_dict = attr_blocking(plain_data_dict, blk_attr_list)
   
  enc_blk_dict   = phoneticBlocking(enc_data_dict, blk_attr_list)
  plain_blk_dict = phoneticBlocking(plain_data_dict, blk_attr_list)
   
  print 'Data are blocked using the attribute values:',
  for i in blk_attr_list:
    print enc_header_list[i],
  print

  # Calculate the accuracy of the blokcing
  #
  pc, cand_rec_id_pairs = pairs_completeness(enc_blk_dict, plain_blk_dict, true_match_id_set)
   
  print '  Blocking technique pairs completeness: %.3f' %pc
  print

# Define a missing value percentage and remove attributes that do not
# meet at least the defined minimum limit
missing_perc_limit = 15.0

# A list of attributes to consider for creating attribute combinations
condsider_attr_num_list = []

# Minimum frequency for plain-text combination value distributions
distr_min_freq = 2

remove_attr_num_list = ATTR_SELECT_DICT[dataset_name_str]['REMOVE_ATTR_LIST']

for attr_index in attack_attr_list:
  
  if(attr_index not in remove_attr_num_list):
    
    elem_index = attack_attr_list.index(attr_index)
    
    enc_missing_perc = enc_missing_perc_list[elem_index]
    plain_missing_perc = plain_missing_perc_list[elem_index]
    
    if(enc_missing_perc < missing_perc_limit and 
       plain_missing_perc < missing_perc_limit):
      
      condsider_attr_num_list.append(elem_index) 

# Calculate the number of same and different values in each attribute,
# attribute pairs, and match keys in true matches 

calc_same_diff_count_flag = False

if(calc_same_diff_count_flag):

  # Calculate the number of same and different values in each attribute,
  # attribute pairs, and match keys compared to true matches 
  #
  attr_same_diff_count_dict, m_key_same_diff_count_dict = \
                              get_same_diff_val_count(enc_data_dict, 
                                                      plain_data_dict, 
                                                      true_match_id_set, 
                                                      enc_header_list)
  
  
  
  for attr in attr_same_diff_count_dict.keys():
    
    same_count = attr_same_diff_count_dict[attr][0]
    diff_count = attr_same_diff_count_dict[attr][1]
    
    num_true_matches = len(true_match_id_set)
    same_perc = 100*float(same_count)/num_true_matches
    diff_perc = 100*float(diff_count)/num_true_matches
  
    print 'Attribute:', attr
    print ' - Same percentage: %.4f' %same_perc
    print ' - Diff percentage: %.4f' %diff_perc
    print
  
  sys.exit()
  
  # Write precision/recall results to a file
  #
  today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
  
  res_file_name = 'pprl_match_key_num_same_diff_count_res.csv'
  
  # Generate header line with column names
  #
  header_list = ['today_time_str', 'encode_dataset_name', 
                 'encode_dataset_num_rec', 'plain_dataset_name', 
                 'plain_dataset_num_rec',
                 #
                 'attr_combination', 'number_true_matches',
                 'number_same_val', 'number_diff_val',
                 'percentage_of_same_val', 'percentage_of_diff_val'
                 #
                ]
  
  #Create result line to write into csv
    
  for attr_comb in m_key_same_diff_count_dict.keys():
    
    attr_list = []
    
    for attr_num in attr_comb:
      attr_list.append(enc_header_list[attr_num])
    
    same_count = m_key_same_diff_count_dict[attr_comb][0]
    diff_count = m_key_same_diff_count_dict[attr_comb][1]
    
    num_true_matches = len(true_match_id_set)
    same_perc = 100*float(same_count)/num_true_matches
    diff_perc = 100*float(diff_count)/num_true_matches
  
    res_list = [today_time_str, encode_base_data_set_name, len(enc_data_dict),
                plain_base_data_set_name, len(plain_data_dict),
                #
                attr_list, len(true_match_id_set), 
                same_count, diff_count,
                same_perc, diff_perc
                #
               ]
  
  
    # Check if the result file exists, if it does append, otherwise create
    #
    if (not os.path.isfile(res_file_name)):
      write_file = open(res_file_name, 'w')
      csv_writer = csv.writer(write_file)
    
      csv_writer.writerow(header_list)
    
      print 'Created new result file:', res_file_name
    
    else:  # Append results to an existing file
      write_file = open(res_file_name, 'a')
      csv_writer = csv.writer(write_file)
    
      print 'Append results to file:', res_file_name
    
    csv_writer.writerow(res_list)
    write_file.close()
  
  sys.exit()

# For each considered attribute calculate the agreement and disagreement weights
# based on the ground truth. This method works if we only have the ground truth
#
attr_weight_dict = calculate_agree_disagree_weights(enc_data_dict, 
                                                    plain_data_dict, 
                                                    enc_unique_val_dict, 
                                                    plain_unique_val_dict, 
                                                    condsider_attr_num_list)

print 'Agreeement/Disagreement weights for each attribute'

used_attr_list = []

for attr_index in attr_weight_dict.keys():
  agree_w = attr_weight_dict[attr_index][0]
  disagree_w = attr_weight_dict[attr_index][1]
  print '  - %s : [Agree: %.4f, Disagree: %.4f]' %(enc_header_list[attr_index], agree_w, disagree_w)
  
  used_attr_list.append(enc_header_list[attr_index])

print

if (run_method == 'linkage'):
  
  prev_f_measure = 0.0
  curr_index = 0
  
  prec_rec_dict = {}
  prec_list  = []
  rec_list   = []
  f_mea_list = []
  
  # Flag for deciding whether we want to do the linkage for all
  # individual match-keys that can be creted using the selected
  # set of attribues
  #
  ind_match_key_link_flag = True 
  min_prec = 0.3
  
  if(ind_match_key_link_flag):
  
    attr_flag_comb_obj = list(itertools.product([0, 1], repeat=len(condsider_attr_num_list)))
    
    attr_comb_list = []
    
    for attr_flag_comb in attr_flag_comb_obj:
      
      select_attr_num_list = []
      
      for flag_index, flag_val in enumerate(attr_flag_comb):
        
        if(flag_val == 1):
          select_attr_num_list.append(condsider_attr_num_list[flag_index])
  
      if(len(select_attr_num_list) == 0):
        continue
      
      attr_comb_list.append(select_attr_num_list)
      
    
    sorted_attr_comb_list = sorted(attr_comb_list, key=lambda x: len(x), reverse=True)
    
    for select_attr_list in sorted_attr_comb_list:
      
      attr_comb_score = 0.0
      attr_name_list = []
      
      for attr_num in condsider_attr_num_list:
        if(attr_num in select_attr_list):
          attr_comb_score += attr_weight_dict[attr_num][0]
          attr_name_list.append(enc_header_list[attr_num])
        else:
          attr_comb_score += attr_weight_dict[attr_num][1]
      
      linkage_res_tuple = single_match_key_record_linkage(enc_data_dict, 
                                                          plain_data_dict, 
                                                          select_attr_list,
                                                          len(true_match_id_set))
      
      
      matched_rec_pairs = linkage_res_tuple[0]
      prec_val          = linkage_res_tuple[1]
      reca_val          = linkage_res_tuple[2]
      f_measure         = linkage_res_tuple[3]
      num_tp            = linkage_res_tuple[4]
      num_fp            = linkage_res_tuple[5]
      num_tn            = linkage_res_tuple[6]
      num_fn            = linkage_res_tuple[7]
      
      print 'Linkage results for individual match-key: %s' %attr_name_list
      print '  Weight score:              %.3f' %attr_comb_score
      print '  Precision:                 %.3f' %prec_val
      print '  Recall:                    %.3f' %reca_val
      print '  F-measure:                 %.3f' %f_measure
      print '----------------------------------------'
      print '  Number of true positives : %d' %num_tp
      print '  Number of false positives: %d' %num_fp
      print '  Number of true negatives : %d' %num_tn
      print '  Number of false negatives: %d' %num_fn
      print
      
      # Write precision/recall results to a file
      #
      today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
  
      res_file_name = 'pprl_single_match_key_linkage_res.csv'
      
      # Generate header line with column names
      #
      header_list = ['today_time_str', 'encode_dataset_name', 
                     'encode_dataset_num_rec', 'plain_dataset_name', 
                     'plain_dataset_num_rec', 'used_attr_list',
                     #
                     'attr_combination', 'weighted_score',
                     'precision', 'recall', 'f-measure',
                     'num_true_positives', 'num_false_positives',
                     'num_true_negatives', 'num_false_negatives',
                     #
                    ]
      
      #Create result line to write into csv
      
      res_list = [today_time_str, encode_base_data_set_name, len(enc_data_dict),
                  plain_base_data_set_name, len(plain_data_dict), used_attr_list,
                  #
                  attr_name_list, attr_comb_score, prec_val, reca_val, f_measure,
                  num_tp, num_fp, num_tn, num_fn,
                  #
                 ]
      
      
      # Check if the result file exists, if it does append, otherwise create
      #
      if (not os.path.isfile(res_file_name)):
        write_file = open(res_file_name, 'w')
        csv_writer = csv.writer(write_file)
      
        csv_writer.writerow(header_list)
      
        print 'Created new result file:', res_file_name
      
      else:  # Append results to an existing file
        write_file = open(res_file_name, 'a')
        csv_writer = csv.writer(write_file)
      
        print 'Append results to file:', res_file_name
      
      csv_writer.writerow(res_list)
      write_file.close()
      
      print '  Written result line:'
      print ' ', res_list
      
      assert len(res_list) == len(header_list)
      
      print
      print '='*80
      print
      
      if(prec_val < min_prec):
        break
  
  else:
    
    max_attr_weight = sum([attr_weight_dict[attr][0] for attr in attr_weight_dict.keys()])
    
    min_weight_score_list = []
    w = -10.0
    
    while(w <= max_attr_weight + 1):
      min_weight_score_list.append(w)
      w += 1.0 # 0.5
      
    prev_attr_comb_list = []
    prev_prec_val   = 0.0
    prev_reca_val   = 0.0
    prev_f_measure  = 0.0
    prev_num_tp     = 0
    prev_num_fp     = 0
    prev_num_tn     = 0
    prev_num_fn     = 0
    
    #min_weight_score_list = [0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
    
    for weighted_score in sorted(min_weight_score_list, reverse=True):
   
      min_weight_score = weighted_score
       
      attr_comb_list = get_attr_comb_above_thresh(attr_weight_dict, min_weight_score)
       
      print 'Found %d attribute combinations that meet the ' %len(attr_comb_list) +\
        'minimum summed weight score of %.2f' %min_weight_score
      print '  Actual attribute combinations selected:', attr_comb_list
      print
      
       
      if(len(attr_comb_list) == 0):
        continue
         
      else:
        
        if(prev_attr_comb_list == attr_comb_list):
          
          print 'Previous attribute combination is the same as current attribute combination'
          print '  Assiging same values...'
          
          prec_val          = prev_prec_val
          reca_val          = prev_reca_val
          f_measure         = prev_f_measure
          num_tp            = prev_num_tp
          num_fp            = prev_num_fp
          num_tn            = prev_num_tn
          num_fn            = prev_num_fn
        
        else:
          linkage_res_tuple = match_key_record_linkage_n(enc_data_dict, 
                                                         plain_data_dict,
                                                         attr_comb_list,
                                                         len(true_match_id_set))
          
          #=====================================================================
          # linkage_res_tuple = record_linkage_with_missing(enc_data_dict, 
          #                                                plain_data_dict,
          #                                                attr_comb_list,
          #                                                len(true_match_id_set))
          #=====================================================================
          
          matched_rec_pairs = linkage_res_tuple[0]
          prec_val          = linkage_res_tuple[1]
          reca_val          = linkage_res_tuple[2]
          f_measure         = linkage_res_tuple[3]
          num_tp            = linkage_res_tuple[4]
          num_fp            = linkage_res_tuple[5]
          num_tn            = linkage_res_tuple[6]
          num_fn            = linkage_res_tuple[7]
          
          prev_attr_comb_list = attr_comb_list
          prev_prec_val   = prec_val
          prev_reca_val   = reca_val
          prev_f_measure  = f_measure
          prev_num_tp     = num_tp
          prev_num_fp     = num_fp
          prev_num_tn     = num_tn
          prev_num_fn     = num_fn
      
      print 'Linkage results match-keys with score above: %.2f' %min_weight_score
      print '  Number of attribute combinations selected: %d' %len(attr_comb_list)
      print '  Precision:                 %.3f' %prec_val
      print '  Recall:                    %.3f' %reca_val
      print '  F-measure:                 %.3f' %f_measure
      print '----------------------------------------'
      print '  Number of true positives : %d' %num_tp
      print '  Number of false positives: %d' %num_fp
      print '  Number of true negatives : %d' %num_tn
      print '  Number of false negatives: %d' %num_fn
      
       
      prec_rec_dict[min_weight_score] = [prec_val, reca_val, f_measure]
      prec_list.append(prec_val)
      rec_list.append(reca_val)
      f_mea_list.append(f_measure)
       
      # Write precision/recall results to a file
      #
      today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
   
      res_file_name = 'pprl_match_key_linkage_res.csv'
       
      # Generate header line with column names
      #
      header_list = ['today_time_str', 'encode_dataset_name', 
                     'encode_dataset_num_rec', 'plain_dataset_name', 
                     'plain_dataset_num_rec', 'used_attr_list',
                     #
                     'weighted_score', 'num_attr_comb_found',
                     #
                     'precision', 'recall', 'f-measure',
                     'num_true_positives', 'num_false_positives',
                     'num_true_negatives', 'num_false_negatives',
                     #
                    ]
       
      #Create result line to write into csv
       
      res_list = [today_time_str, encode_base_data_set_name, len(enc_data_dict),
                  plain_base_data_set_name, len(plain_data_dict), used_attr_list,
                  #
                  min_weight_score, len(attr_comb_list),
                  #
                  prec_val, reca_val, f_measure, num_tp, num_fp, num_tn, 
                  num_fn,
                  #
                 ]
       
       
      # Check if the result file exists, if it does append, otherwise create
      #
      if (not os.path.isfile(res_file_name)):
        write_file = open(res_file_name, 'w')
        csv_writer = csv.writer(write_file)
       
        csv_writer.writerow(header_list)
       
        print 'Created new result file:', res_file_name
       
      else:  # Append results to an existing file
        write_file = open(res_file_name, 'a')
        csv_writer = csv.writer(write_file)
       
        print 'Append results to file:', res_file_name
       
      csv_writer.writerow(res_list)
      write_file.close()
       
      print '  Written result line:'
      print ' ', res_list
       
      assert len(res_list) == len(header_list)
       
      print
      print '='*80
      print
      
      if(prec_val < min_prec):
        break
       
    # Create the general blog and the "subplots" i.e. the bars
    w,h = plt.figaspect(ASPECT_RATIO)
    f, ax1 = plt.subplots(1, figsize=(w,h))
     
    plt_x_data = [i for i in range(1,len(min_weight_score_list)+1)]
     
    ax1.plot(plt_x_data, prec_list, linewidth=1, label='Precision')
    ax1.plot(plt_x_data, rec_list, linewidth=1, label='Recall')
    ax1.plot(plt_x_data, f_mea_list, linewidth=1, label='F-measure')
     
    ax1.set_xlabel('Score threshold',fontsize=PLT_FONT_SIZE)
    ax1.set_ylabel('Prec/Recall/F-measure',fontsize=PLT_FONT_SIZE)
     
    plt.yticks(fontsize=TICKS_FONT_SIZE)
     
    plt.xticks(numpy.arange(1,len(min_weight_score_list)+1), min_weight_score_list, 
               fontsize=X_TICKS_FONT_SIZE, rotation=45)
     
    #ax1.set_xticklabels(min_weight_score_list)
     
    #dataset_match_perc = plain_base_data_set_name.split('-')[4]
    #dataset_num_changes = plain_base_data_set_name.split('-')[2]
    encode_dataset_year = encode_base_data_set_name.split('-')[1]
    plain_dataset_year  = plain_base_data_set_name.split('-')[1]
     
    plt_title = 'Linkage accuracy (%s, %s)' \
                %(encode_dataset_year, plain_dataset_year)
     
    #plt_file = 'pprl-match-keys-linkage-results-%s-%s' % \
    #             (encode_base_data_set_name, plain_base_data_set_name)
     
    plt_file = 'pprl-match-keys-linkage-results-%s-%s' %(encode_dataset_year, 
                                                         plain_dataset_year)
                   
    for attr_num in condsider_attr_num_list:
      plt_file += '-' + ATTR_SELECT_DICT[dataset_name_str]['ENC_ATTR_NAMES_DICT'][attr_num]
     
    plt_file_name = plt_file + FILE_FORMAT
     
    plt.title(plt_title,fontsize=TITLE_FONT_SIZE)
    plt.legend(fontsize=LEGEND_FONT_SIZE, loc='best')
     
    #plt.show()
    plt.savefig(plt_file_name, bbox_inches='tight')
  
  

elif(run_method == 'attack'): # Run the attack
  
  # Get the attribute combinations that meets the minimum weight score. At the
  # same time apply superset pruning to remove all the attribute combinations 
  # that is covered by one of its subsets.
  # 
  attr_comb_list = get_attr_comb_above_thresh(attr_weight_dict, min_weight_score)
  
  print 'Found %d attribute combinations that meets the ' %len(attr_comb_list) +\
        'minimum summed weight score of %.2f' %min_weight_score
  print '  Actual attribute combinations selected:', attr_comb_list
  print 
  
  # Encode plain-text values using given set of attribute combinations
  # and create a list of match keys for each record. The following
  # method returns a dictionary with keys being record identifiers
  # and values being the list of match keys.
  #
  enc_match_key_dict, enc_unique_match_key_dict = create_match_key_dict\
                                                  (enc_data_dict, attr_comb_list)
  
  sorted_attr_comb_list = sorted(attr_comb_list, key=lambda x: len(x), reverse=True)
  
  # Run improvement to the match-key protocol
  run_improv = False
  
  if(run_improv):
    # Calculate the frequency distribution of match keys in encoded dataset
    match_key_freq_dict = compute_match_key_freq_solution(enc_match_key_dict)
  else:
    # Calculate the frequency distribution of match keys in encoded dataset
    match_key_freq_dict = compute_match_key_freq(enc_match_key_dict)
  
  
  print_match_key_freq = False
  
  if(print_match_key_freq):
    
    attr_indices = print_num_match_key_diff_freq(match_key_freq_dict)
    
    attr_index_set = set()
    
    for attr_index in attr_indices:
      attr_index_set.add((enc_header_list[attr_index], attr_index))
    
    print 'Attribte indices:', attr_index_set 
  
  # How many top frequent values from a frequency distribution is considered
  top_k = consdrd_top_num_val
  
  # A dictionary with identified attribute combinations and plain-text values
  # for top k frequent values
  identified_val_dict = {}
  
  # A dictionary with identified attribute combinations
  ident_attr_comb_dict = {}
  
  print 'Conduct the frequency attack on match key database to identify the' +\
        ' encoded attribute combinations and plain-text values'
  print
  
  #========================================================================= 
  
  if(attack_step == 'main'):
    
    pt_freq_start_time = time.time()
    
    if(attacker_knwlge == 'attr'):
      attak_used_attr_num_list = condsider_attr_num_list
      
      # Number of attributes considered for the attack
      num_attr = len(attak_used_attr_num_list)
      
    elif(attacker_knwlge == 'dom'):
      #attak_used_attr_num_list = [i for i in range(len(attack_attr_list))]
      attak_used_attr_num_list = []
      
      for i, attr_num in enumerate(attack_attr_list):
        if(attr_num in [5, 7, 14, 15, 17]):
          attak_used_attr_num_list.append(i)
      
      # Number of attributes considered for the attack
      num_attr = len(attak_used_attr_num_list)
      
    elif(attacker_knwlge == 'comb'):
      analysis_attr_comb_list = attr_comb_list
      
      num_attr = len(analysis_attr_comb_list)
      
      # Get plain text frequency disctionary for all created attribute combinations
      plain_text_freq_dict, plain_unique_num_match_key_dict = \
                            compute_plain_text_freq(analysis_attr_comb_list, 
                                                    plain_data_dict, 
                                                    distr_min_freq)
    
    found_attr_comb_dict = {}
    ident_attr_comb_list = []
    
    ident_attr_comb_dict = {}
    
    time_dict = {}
    
    attr_comb_key_dict = {}
    
    if(attacker_knwlge != 'comb'):
      
      pt_freq_start_time = time.time()
      
      full_attr_comb_list = []
      
      for attr_comb_len in range(3, num_attr):
        
        # Create all possible combinations of selected length using attribute indices
        attr_comb_list_obj = itertools.combinations(attak_used_attr_num_list, attr_comb_len)
        
        # Get all attribute combinations to a list
        analysis_attr_comb_list = [attr_comb for attr_comb in attr_comb_list_obj]
        full_attr_comb_list = full_attr_comb_list + analysis_attr_comb_list
    
      # Get plain text frequency disctionary for all created attribute combinations
      plain_text_freq_dict, plain_unique_num_match_key_dict = \
                              compute_plain_text_freq(full_attr_comb_list, 
                                                      plain_data_dict, 
                                                      distr_min_freq)
      
    pt_freq_gen_time = time.time() - pt_freq_start_time
    
    
    stat_res_dict_full      = {}
    stat_res_norm_dict_full = {}
    # Generate similarity matrices for each encoded combination
    # using all possible plain-text combinations
    #
    for true_attr_comb in match_key_freq_dict.keys():
      
      comb_anlyse_start_time = time.time()
      
      plain_comb_sim_matrix = {}
      
      # Get the frequency distribution for this particular match key and 
      # sort the distribution descending order
      enc_sub_freq_dict = match_key_freq_dict[true_attr_comb]
      enc_freq_list = sorted([freq for key, freq in enc_sub_freq_dict.items()],
                              reverse=True)
      
      plain_comb_unique_key_dict = {}
      
      print 'Analysing the encoded combination %s' %list(true_attr_comb)   
      
      if(attacker_knwlge == 'comb'):
        
        print '  - Number of attribute combinations analysing: %d' %len(analysis_attr_comb_list)
        print
        
        # Check if there are any attribute combinations of current length which 
        # satisfies the minimum frequency limit. If not break the loop as we
        # cannot find any more combinations with higher combination lengths
        if(len(plain_text_freq_dict) == 0):
          print '  No plain-text attribute combinations are found which has a frequency ' +\
                'distribution with at least %d frequency limit' %distr_min_freq
          print '  Breaking the loop...'
          print
          break

        
        dist_analysis_res_dict = {}
        
        corr_not_selected = []
        
        # List of all the statistical tests used
        stat_test_list = ['mean', 'std', 'var', 'skew', 'emd', 'hist', 'ksstat', 
                          'entrpy', 'pcstat', 'spstat']
        
        plain_comb_stat_res_dict = get_freq_distr_stat_res(plain_text_freq_dict, 
                                                           enc_freq_list, 
                                                           true_attr_comb)
        
        for plain_comb in plain_comb_stat_res_dict.keys():
          stat_res_list = plain_comb_stat_res_dict[plain_comb]
          
          for (i, stat_test) in enumerate(stat_test_list):
            stat_res = stat_res_list[i]
            
            stat_test_dict = plain_comb_sim_matrix.get(stat_test, {})
            stat_test_dict[plain_comb] = stat_res
            plain_comb_sim_matrix[stat_test] = stat_test_dict
        
      else:
        
        # List of all the statistical tests used
        stat_test_list = ['mean', 'std', 'var', 'skew', 'emd', 'hist', 'ksstat', 
                          'entrpy', 'pcstat', 'spstat']
        
        plain_comb_stat_res_dict = get_freq_distr_stat_res(plain_text_freq_dict, 
                                                           enc_freq_list, 
                                                           true_attr_comb)
        
        
        for plain_comb in plain_comb_stat_res_dict.keys():
          stat_res_list = plain_comb_stat_res_dict[plain_comb]
          
          #print stat_res_list
          
          for (i, stat_test) in enumerate(stat_test_list):
            stat_res = stat_res_list[i]
            
            stat_test_dict = plain_comb_sim_matrix.get(stat_test, {})
            stat_test_dict[plain_comb] = stat_res
            plain_comb_sim_matrix[stat_test] = stat_test_dict
      
      
      stat_res_calc_time = time.time() - comb_anlyse_start_time
      
      cand_pt_start_time = time.time()
      
      plain_comb_stat_res_dict_norm = {}
      
      # Normalise the values in matrix
      #
      ranked_plain_comb_matrix = {}
      
      stat_res_norm_dict = {}
      stat_res_dict      = {}
      
      for stat_test in plain_comb_sim_matrix.keys():
        stat_test_dict = plain_comb_sim_matrix[stat_test]
        
        plain_comb_list = []
        plain_val_list  = []
        
        for plain_comb, stat_val in stat_test_dict.iteritems():
          plain_comb_list.append(plain_comb)
          plain_val_list.append(stat_val)
        
        #print plain_val_list
        if(stat_test in ['mean', 'std', 'var', 'skew', 'emd', 'ksstat', \
                         'entrpy']):
          norm_stat_val_list = min_max_normalise(plain_val_list, True)
        else:
          norm_stat_val_list = min_max_normalise(plain_val_list)
        
        #print norm_stat_val_list
        stat_test_index = stat_test_list.index(stat_test)
        
        if(min(norm_stat_val_list) == 0.0 and max(norm_stat_val_list) == 0.0):
          continue
        
        new_stat_test_dict = {}
        for i, plain_comb in enumerate(plain_comb_list):
          norm_stat_val = norm_stat_val_list[i]
          org_stat_val  = plain_val_list[i]
          new_stat_test_dict[plain_comb] = [norm_stat_val, org_stat_val]
          
          norm_stat_res_list = plain_comb_stat_res_dict_norm.get(plain_comb, ['' for _ in range(len(stat_test_list))])
          norm_stat_res_list[stat_test_index] = norm_stat_val
          plain_comb_stat_res_dict_norm[plain_comb] = norm_stat_res_list       
        
        ranked_comb_list = sorted(new_stat_test_dict.items(), key=lambda x: x[1][0], reverse=True)
        
        max_val_diff = 5
        filtered_comb_list = []
        
        filtered_comb_set = set()
        
        for i in range(len(ranked_comb_list) - 2):
           
          plain_comb_1   = ranked_comb_list[i][0]
          stat_res_val_1 = ranked_comb_list[i][1][0]
          org_stat_val_1 = ranked_comb_list[i][1][1]
          
          plain_comb_2   = ranked_comb_list[i+1][0]
          stat_res_val_2 = ranked_comb_list[i+1][1][0]
          org_stat_val_2 = ranked_comb_list[i+1][1][1]
          
          stat_val_diff = 100*(stat_res_val_1 - stat_res_val_2)/((stat_res_val_1 + stat_res_val_2)/2.0)
           
          if(stat_val_diff <= max_val_diff):
            filtered_comb_list.append((plain_comb_1, stat_res_val_1, org_stat_val_1))
            filtered_comb_set.add(plain_comb_1)
          else:
            filtered_comb_list.append((plain_comb_1, stat_res_val_1, org_stat_val_1))
            filtered_comb_set.add(plain_comb_1)
            break
        
        
        for plain_comb in filtered_comb_set:
          
          plain_unique_num_match_keys = plain_unique_num_match_key_dict[plain_comb]
          enc_unique_num_match_keys = len(enc_freq_list)
        
          num_match_key_diff = 2*float(abs(plain_unique_num_match_keys - enc_unique_num_match_keys))/(plain_unique_num_match_keys + enc_unique_num_match_keys)
          
          print 'Plain comb:', plain_comb
          print 'Enc-freq: %d    Plain-freq: %d' %(enc_unique_num_match_keys, plain_unique_num_match_keys)
          print 'Diff percentage: ', num_match_key_diff
          print 
          
          stat_res_dict[plain_comb]      = plain_comb_stat_res_dict[plain_comb]
          stat_res_norm_dict[plain_comb] = plain_comb_stat_res_dict_norm[plain_comb]
          
        
        ranked_plain_comb_matrix[stat_test] = filtered_comb_list
        
      
      cand_pt_slct_time = time.time() - cand_pt_start_time
      
      time_dict[true_attr_comb] = [stat_res_calc_time, cand_pt_slct_time]
        
      stat_res_dict_full[true_attr_comb]      = stat_res_dict
      stat_res_norm_dict_full[true_attr_comb] = stat_res_norm_dict
        
      del plain_comb_sim_matrix
      
      ident_attr_comb_dict[true_attr_comb] = ranked_plain_comb_matrix
    
    # Writing results to a csv
    #
    today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
    
    encode_dataset_year = encode_base_data_set_name.split('-')[1]
    plain_dataset_year  = plain_base_data_set_name.split('-')[1]
    
    res_file_name = 'pprl_match_key_attack_res_%s_%s.csv' %(encode_dataset_year, plain_dataset_year)
    
    time_res_file = 'pprl_match_key_attack_time_res_%s_%s.csv' %(encode_dataset_year, plain_dataset_year)
    
    # Generate header line with column names
    #
    header_list = ['today_time_str', 'attacker_knowledge', 'true_attr_comb', 
                   'selected_attr_comb',
                   #
                   'mean_sim_norm', 'std_sim_norm', 'var_sim_norm', 
                   'skew_sim_norm', 'emd_sim_norm', 'histogram_intesec_norm', 
                   'ks_sim_norm', 'entropy_sim_norm', 'pearson_sim_norm', 
                   'spearman_sim_norm',
                   #
                   'mean_sim_org', 'std_sim_org', 'var_sim_org', 
                   'skew_sim_org', 'emd_sim_org', 'histogram_intesec_org', 
                   'ks_sim_org', 'entropy_sim_org', 'pearson_sim_org', 
                   'spearman_sim_org',
                   #
                   'unique_num_m_key_diff',
                  ]
    
    # Generate header line with column names
    #
    time_header_list = ['today_time_str', 'attacker_knowledge', 'true_attr_comb', 
                        'num_analysed_attr',
                         #
                         'freq_distr_gen_time', 'corr_calc_time', 'cand_select_time',
                         ]
    
    for true_attr_comb in time_dict.keys():
      time_list = time_dict[true_attr_comb]
      
      res_list = [today_time_str, attacker_knwlge, true_attr_comb, num_attr, 
                  pt_freq_gen_time]
      
      res_list += time_list
      
      # Check if the result file exists, if it does append, otherwise create
      if (not os.path.isfile(time_res_file)):
        write_file = open(time_res_file, 'w')
        csv_writer = csv.writer(write_file)
      
        csv_writer.writerow(time_header_list)
      
        print 'Created new result file:', time_res_file
      
      else:  # Append results to an existing file
        write_file = open(time_res_file, 'a')
        csv_writer = csv.writer(write_file)
      
        print 'Append results to file:', time_res_file
      
      csv_writer.writerow(res_list)
      write_file.close()
      
      print '  Written result line:'
      print ' ', res_list
      print
    
    final_res_analyse_dict = {}
    
    for true_attr_comb in ident_attr_comb_dict.keys():
      plain_comb_matrix = ident_attr_comb_dict[true_attr_comb]
      
      stat_res_norm_dict = stat_res_norm_dict_full[true_attr_comb]
      stat_res_dict = stat_res_dict_full[true_attr_comb]
      
      plain_comb_res_dict = {}
      
      print
      print '########################'
      print 'Results for encode attribute combination: %s' %list(true_attr_comb)
      for stat_test in plain_comb_matrix.keys():
        ranked_comb_list = plain_comb_matrix[stat_test]
        stat_test_index = stat_test_list.index(stat_test)
        
        print '  Statistical test: %s' %stat_test
        print '  Top selected plain-text combinations'
        
        for (plain_comb, norm_stat_val, org_stat_val) in ranked_comb_list:
          print '   - %s : %.8f, %.8f' %(plain_comb, norm_stat_val, org_stat_val)
          
          res_list_pair = plain_comb_res_dict.get(plain_comb, [['' for _ in range(len(stat_test_list))] for _ in range(2)])
          res_list_pair[0][stat_test_index] = norm_stat_val
          res_list_pair[1][stat_test_index] = org_stat_val
          
          plain_comb_res_dict[plain_comb] = res_list_pair         
        
        print
      
      # Filter plain-text attribute combinations by analysing unique number of hash values for 
      # certain attribute combinations
      enc_sub_freq_dict = match_key_freq_dict[true_attr_comb]
      enc_unique_num_match_keys = len(enc_sub_freq_dict)
      
      for plain_comb in plain_comb_res_dict.keys():
        plain_stat_res_list_pair = plain_comb_res_dict[plain_comb]
        
        # Filter plain-text combinations
        #
        plain_unique_num_match_keys = plain_unique_num_match_key_dict[plain_comb]
        
        num_match_key_diff = 200*float(abs(plain_unique_num_match_keys - enc_unique_num_match_keys))/(plain_unique_num_match_keys + enc_unique_num_match_keys)
        
        #Create result line to write into csv
        res_list = [today_time_str, attacker_knwlge, true_attr_comb]
        res_list.append(plain_comb)
        res_list += stat_res_norm_dict[plain_comb]
        res_list += stat_res_dict[plain_comb]
        res_list.append(num_match_key_diff)
        
        
        # Add results to final results dict
        plain_comb_analyse_dict = final_res_analyse_dict.get(true_attr_comb, {})
        plain_comb_analyse_dict[plain_comb] = [stat_res_norm_dict[plain_comb], num_match_key_diff]
        final_res_analyse_dict[true_attr_comb] = plain_comb_analyse_dict
        
        # Check if the result file exists, if it does append, otherwise create
        if (not os.path.isfile(res_file_name)):
          write_file = open(res_file_name, 'w')
          csv_writer = csv.writer(write_file)
        
          csv_writer.writerow(header_list)
        
          print 'Created new result file:', res_file_name
        
        else:  # Append results to an existing file
          write_file = open(res_file_name, 'a')
          csv_writer = csv.writer(write_file)
        
          print 'Append results to file:', res_file_name
        
        csv_writer.writerow(res_list)
        write_file.close()
        
        print '  Written result line:'
        print ' ', res_list
        print
    
    
  elif(attack_step == 're-ident')  
    
    # Re-identify plain-text values using identified plain-text match-keys for each
    # encoded match-key
    
    pt_comb_ident_start_time = time.time()
    
    col_sep_char = ','
    
    if('20190803' in plain_base_data_set_name):
      file_name = 'pprl_match_key_attack_res_20191001_20190803.csv'
    elif('20190203' in plain_base_data_set_name):
      file_name = 'pprl_match_key_attack_res_20191001_20190203.csv'
    elif('20181003' in plain_base_data_set_name):
      file_name = 'pprl_match_key_attack_res_20191001_20181003.csv'
    elif('20171003' in plain_base_data_set_name):
      file_name = 'pprl_match_key_attack_res_20191001_20171003.csv'
    elif('20111004' in plain_base_data_set_name):
      file_name = 'pprl_match_key_attack_res_20191001_20111004.csv'

    if (file_name.endswith('gz')):
      f = gzip.open(file_name)
    else:
      f = open(file_name)
      
    print
    print 'Load data set from file:', file_name
    print '  Attribute separator: %c' % (col_sep_char)
    
    csv_reader = csv.reader(f, delimiter=col_sep_char)
    header_line = True
    
    if (header_line == True):
      header_list = csv_reader.next()
      print '  Header line:', header_list
    
    res_dict = {}
    
    plain_comb_set = set()
    
    for (j, data_rec) in enumerate(csv_reader):
      
      true_comb = data_rec[2]
      guessed_comb = data_rec[3]
      
      plain_comb_set.add(guessed_comb)
      
      sim_val_list = []
      
      sim_val_norm_list = []
      sim_val_org_list  = []
      uniq_m_key_diff   = 0.0
      
      num_empty = 0
      for i, rec_val in enumerate(data_rec[4:]):
        
        if(len(rec_val) > 0):
          input_val = float(rec_val)
        else:
          num_empty += 1
          input_val = 0.0
        
        if(i <= 9):
          sim_val_norm_list.append(input_val)
        elif(i <= 19):
          sim_val_org_list.append(input_val)
        else:
          uniq_m_key_diff = input_val
    
      assert len(sim_val_norm_list) == len(sim_val_org_list) == 10
      
      comb_res_dict = res_dict.get(true_comb, {})
      comb_res_dict[guessed_comb] = [sim_val_norm_list, uniq_m_key_diff]
      res_dict[true_comb] = comb_res_dict
    
    final_res_analyse_dict = res_dict
    
    # Assign plain-text combinations to encoded combinations by analysing the normalised
    # similarity results
    
    assign_res_dict = {}
    ident_plain_comb_list = []

    assignment_method = 'greedy' # 'munkres'
    sim_val_w = 0.7
    uniq_mk_val_w = 0.3
    
    if(assignment_method == 'greedy'):
      #Greedy assignment (without any filtering)
      #
      for true_comb in final_res_analyse_dict.keys():
         
        filtered_comb_dict = {}
         
        comb_res_dict = final_res_analyse_dict[true_comb]
         
        print 'True combination:', true_comb
         
         
        for plain_comb in comb_res_dict.keys():
          m_key_diff = comb_res_dict[plain_comb][1]
          norm_sim_val_list = comb_res_dict[plain_comb][0]
           
          sim_val_mean = numpy.mean(norm_sim_val_list)
           
          weighted_avrg = sim_val_mean*sim_val_w + (1.0-(m_key_diff/100))*uniq_mk_val_w
           
          filtered_comb_dict[plain_comb] = weighted_avrg
         
        ranked_comb_list = sorted(filtered_comb_dict.items(), key=lambda x: x[1], reverse=True)
        
        assign_res_dict[true_comb] = [ranked_comb_list[0]]
        ident_plain_comb_list.append(ranked_comb_list[0][0])
         
        print 'Filtered combinations:'
         
        for comb, val in ranked_comb_list[:5]:
          print ' - %s : %.7f' %(comb, val)
        
        print
      
    else: # Munkres assignment

      true_comb_list = final_res_analyse_dict.keys()
      plain_comb_list = list(plain_comb_set)
       
      asgn_array = numpy.ones((len(true_comb_list), len(plain_comb_list)))
       
      for i, true_comb in enumerate(true_comb_list):
         
        filtered_comb_dict = {}
         
        comb_res_dict = final_res_analyse_dict[true_comb]  
         
        for j, plain_comb in enumerate(plain_comb_list):
           
          if(plain_comb in comb_res_dict):
            m_key_diff = comb_res_dict[plain_comb][2]
            norm_sim_val_list = comb_res_dict[plain_comb][0]
            sim_val_mean = numpy.mean(norm_sim_val_list)
             
            weighted_avrg = sim_val_mean*sim_val_w + (1.0-(m_key_diff/100))*uniq_mk_val_w
            asgn_array[i][j] = 1.0 - weighted_avrg     
             
      assign_res_row, assign_res_col = optimize.linear_sum_assignment(asgn_array)
       
      for i in assign_res_row:
        print 'True combination:', true_comb_list[i]
        print 'Filtered combination:', plain_comb_list[assign_res_col[i]], (1-asgn_array[i][assign_res_col[i]])
        print 
        
        assign_res_dict[true_comb_list[i]] = [plain_comb_list[assign_res_col[i]], (1-asgn_array[i][assign_res_col[i]])]
    
    pt_comb_ident_time = time.time() - pt_comb_ident_start_time

    #Plain-text alignment
    #    
    pt_align_start_time = time.time()
    
    plain_freq_val_dict = {}
    
    # Adjust the attribute indices. If same attribute combinations are used
    # keep it as it is.
    comb_dict = {0:0, 1:1, 2:2, 3:3, 4:4, 5:5, 6:6, 7:7, 8:8, 9:9, 10:10}
    
    # Calculate frequency distributions and get plain-text ids for
    # identified plain-text combinations. This is to identify exact
    # individual records that can be re-identified
    #
    plain_comb_list = []
    
    for plain_comb in ident_plain_comb_list:
      
      plain_comb = plain_comb.replace('(', '')
      plain_comb = plain_comb.replace(')', '')
      
      attr_comb_list = [int(i) for i in plain_comb.split(',')]
      plain_comb = tuple(attr_comb_list)
      
      temp_plain_comb = []
    
      for comb in plain_comb:
        temp_plain_comb.append(comb_dict[comb])
    
      plain_comb = tuple(temp_plain_comb)
      plain_comb_list.append(plain_comb)
      
    ident_plain_id_dict = ident_comb_plain_text_id_set(plain_comb_list, plain_data_dict)
    
    
    top_k = 5
    freq_diff_limit = 20.0
    
    reident_1_to_1_dict = {}
    
    for true_comb in assign_res_dict:
      poss_attr_comb_list = assign_res_dict[true_comb]
      
      true_comb = true_comb.replace('(', '')
      true_comb = true_comb.replace(')', '')
      
      true_comb_list = [int(i) for i in true_comb.split(',')]
      true_comb = tuple(true_comb_list)
      
      act_comb_list = []
      
      for comb in true_comb:
        act_comb_list.append(comb_dict[comb])
      
      true_comb = tuple(act_comb_list)
      
      enc_sub_freq_dict = match_key_freq_dict[true_comb]
      enc_freq_list = sorted(enc_sub_freq_dict.items(), key=lambda x: x[1], 
                             reverse=True)
      
      print '#### True attrbute combination:', true_comb
      print
    
      for attr_comb, sim_val in poss_attr_comb_list:
        
        ident_plain_val_dict = {}
        
        attr_comb = attr_comb.replace('(', '')
        attr_comb = attr_comb.replace(')', '')
        
        attr_comb_list = [int(i) for i in attr_comb.split(',')]
        attr_comb = tuple(attr_comb_list)
        
        act_plain_comb = []
      
        for comb in attr_comb:
          act_plain_comb.append(comb_dict[comb])
      
        attr_comb = tuple(act_plain_comb)
        
        plain_sub_freq_dict = plain_text_freq_dict[attr_comb]
        plain_freq_list = sorted(plain_sub_freq_dict.items(), key=lambda x: x[1], 
                                 reverse=True)  
        
        true_enc_val_set = set()
        guessed_plain_val_set = set()
        
        # Align top k frequent values from the match key distribution with the 
        # plain-text attribute combination distribution/s
        #
        for index, match_key_freq in enumerate(enc_freq_list):
          
          enc_freq = match_key_freq[1]
          enc_key = match_key_freq[0]
           
          plain_comb_freq = plain_freq_list[index][1]
          plain_comb_val = plain_freq_list[index][0]
           
          freq_diff = 200*float(abs(plain_comb_freq - enc_freq))/(plain_comb_freq + enc_freq)
           
          if(freq_diff > freq_diff_limit):
            print '...Too high frequency difference. Breaking the loop...'
            print
            break
           
          plain_set = set(plain_comb_val.split(','))
          enc_val = enc_unique_match_key_dict[enc_key]
          enc_val_set = set(enc_val.split(','))
          
          plain_id_set = ident_plain_id_dict[attr_comb][plain_comb_val]
           
          plain_val_dict_key = (enc_freq, plain_comb_freq)
          plain_val_list_pair = ident_plain_val_dict.get(plain_val_dict_key, [set(), set(), set()])
           
          true_enc_val_set      = plain_val_list_pair[0]
          guessed_plain_val_set = plain_val_list_pair[1]
          guessed_rec_id_set    = plain_val_list_pair[2]
           
          true_enc_val_set.update(enc_val_set)
          guessed_plain_val_set.update(plain_set)
          guessed_rec_id_set.update(plain_id_set)
          
          ident_plain_val_dict[plain_val_dict_key] = [true_enc_val_set, guessed_plain_val_set, 
                                                      guessed_rec_id_set]
          
          
          for plain_id in plain_id_set:
            
            reident_pair_list = reident_1_to_1_dict.get(plain_id, [set(), set()])
            true_val_set = reident_pair_list[0]
            guessed_val_set = reident_pair_list[1]
            
            true_val_set.update(enc_val_set)
            guessed_val_set.update(plain_set)
            
            reident_1_to_1_dict[plain_id] = [true_val_set, guessed_val_set]
          
           
          if(index < 5):
            print '  - Match key:    ', match_key_freq
            print '  - True value:   ', enc_val
            print '  - Guessed value:', plain_comb_val
            print
 
        # Create a dictionary with identified set of attribute values and true set
        # of attribute values for each combination for evaluation
        # 
        identified_val_dict[(true_comb, attr_comb)] = ident_plain_val_dict
          
          
    print
    print '=========================================='
    print
  
  
    eval_res_tuple = evaluate_attack_res(identified_val_dict)
    
    prec_list           = eval_res_tuple[0]
    reca_list           = eval_res_tuple[1]
    ident_attr_val_dict = eval_res_tuple[2]
    exact_corr_ids      = eval_res_tuple[3]
    part_corr_ids       = eval_res_tuple[4]
    wrng_ids            = eval_res_tuple[5]
    
    num_corr_ident = 0
    num_wrng_ident = 0
    
    x = 0
    
    print ' Length of the id dictionary: ', len(ident_attr_val_dict)
    
    for plain_id, ident_val_set_pair in ident_attr_val_dict.iteritems():
      
      if(x <= 5):
        print plain_id
        print '  Correct', ident_val_set_pair[0]
        print '  Wrong  ', ident_val_set_pair[1]
        print 
      
      num_corr_ident += len(ident_val_set_pair[0])
      num_wrng_ident += len(ident_val_set_pair[1])
      
      x += 1
    
    
    ind_prec_list = []
    ind_rec_list  = []
    
    ind_corr_id_set = set()
    ind_part_corr_id_set = set()
    ind_wrng_id_set = set()
    
    num_ind_corr_ident = 0
    num_ind_wrng_ident = 0
    
    for plain_id, res_list in reident_1_to_1_dict.iteritems():
      
      true_val_set = res_list[0]
      guessed_val_set = res_list[1]
      corr_val_set = true_val_set.intersection(guessed_val_set)
      
      prec_val = float(len(corr_val_set))/len(guessed_val_set)
      rec_val  = float(len(corr_val_set))/len(true_val_set)
      
      if(math.isnan(prec_val) == False):
        ind_prec_list.append(prec_val)
      
      if(math.isnan(rec_val) == False):
        ind_rec_list.append(rec_val)
        
      if(len(corr_val_set) == len(guessed_val_set)):
        ind_corr_id_set.add(plain_id)
      elif(len(corr_val_set) == 0):
        ind_wrng_id_set.add(plain_id)
      else:
        ind_part_corr_id_set.add(plain_id)
      
      num_ind_corr_ident += len(corr_val_set)
      num_ind_wrng_ident += len((guessed_val_set - corr_val_set))
    
    print '###  Overall precision:' + str(prec_list) + ' (%.3f avrg)' %numpy.mean(prec_list)
    print '###  Overall recall:   ' + str(reca_list) + ' (%.3f avrg)' %numpy.mean(reca_list)
    print '###  Number of correctly identified attribute values: ', num_corr_ident
    print '###  Number of wrongly identified attribute values:   ', num_wrng_ident
    print '###  Number of identified exactly correct records: ', len(exact_corr_ids)
    print '###  Number of identified partialy correct records:', len(part_corr_ids)
    print '###  Number of identified wrong records:           ', len(wrng_ids)
    print
    print '###  Number of correctly identified individual records:    ', len(ind_corr_id_set)
    print '###  Number of partially identified individual records:    ', len(ind_part_corr_id_set)
    print '###  Number of wrongly identified individual records:      ', len(ind_wrng_id_set)
    print '###  Number of corect individual attribute identifications:', num_ind_corr_ident
    print '###  Number of wrong individual attribute identifications: ', num_ind_wrng_ident
    print '###  Individual identification precision: %.3f avrg' %numpy.mean(ind_prec_list)
    print '###  Individual identification recall   : %.3f avrg' %numpy.mean(ind_rec_list)
    print
    
    
    pt_align_time = time.time() - pt_align_start_time
    
    encode_dataset_year = encode_base_data_set_name.split('-')[1]
    plain_dataset_year  = plain_base_data_set_name.split('-')[1]
    
    res_file_name = 'pprl_match_key_attack_plain_text_alignment_res_%s_%s.csv' %(encode_dataset_year, plain_dataset_year)

    today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
    
    # Generate header line with column names
    #
    header_list = ['today_time_str', 'encode_dataset_name', 
                   'encode_dataset_num_rec', 'plain_dataset_name', 
                   'plain_dataset_num_rec', 'used_attr_list',
                   'sample_size',
                   #
                   'attacker_knowledge', 'freq_diff_limit',
                   'min_weight_score',
                   #
                   'used_num_attr_comb',
                   #
                   'plain_text_comb_ident_time', 'plain_text_align_time',
                   #
                   'reident_acc_prec', 'reident_acc_reca',
                   #
                   'num_corr_ident', 'num_wrng_ident',
                   'num_exact_corr', 'num_part_corr', 'num_wrng',
                   #
                   'num_ind_corr_rec', 'num_ind_part_rec',
                   'num_ind_wrng_rec', 'num_corr_ind_ident',
                   'num_wrng_ind_ident', 'ind_avrg_prec',
                   'ind_avrg_reca',
                  ]
    
    #Create result line to write into csv
    
    res_list = [today_time_str, encode_base_data_set_name, 
                len(enc_data_dict), plain_base_data_set_name, 
                len(plain_data_dict), used_attr_list,
                sample_size,
                #
                attacker_knwlge, freq_diff_limit, 
                min_weight_score,
                #
                len(attr_comb_list),
                #
                pt_comb_ident_time, pt_align_time,
                #
                numpy.mean(prec_list), numpy.mean(reca_list),
                #
                num_corr_ident, num_wrng_ident,
                len(exact_corr_ids), len(part_corr_ids), len(wrng_ids),
                #
                len(ind_corr_id_set), len(ind_part_corr_id_set),
                len(ind_wrng_id_set), num_ind_corr_ident,
                num_ind_wrng_ident, numpy.mean(ind_prec_list),
                numpy.mean(ind_rec_list),
               ]
    
    
    # Check if the result file exists, if it does append, otherwise create
    #
    if (not os.path.isfile(res_file_name)):
      csv_writer = csv.writer(open(res_file_name, 'w'))
    
      csv_writer.writerow(header_list)
    
      print 'Created new result file:', res_file_name
    
    else:  # Append results to an existing file
      csv_writer = csv.writer(open(res_file_name, 'a'))
    
      print 'Append results to file:', res_file_name
    
    csv_writer.writerow(res_list)
    
    print '  Written result line:'
    print ' ', res_list
    
    assert len(res_list) == len(header_list)
    
    print
    print '='*80
    print
        
# End
    
    


