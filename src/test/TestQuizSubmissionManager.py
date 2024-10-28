import unittest
from unittest.mock import MagicMock, patch
from flask import session
from src.server.QuizSubmissionManager import QuizSubmissionManager

class TestQuizSubmissionManager(unittest.TestCase):
    def setUp(self):
        self.mock_db_manager = MagicMock()
        self.mock_retrieval_manager = MagicMock()
        self.manager = QuizSubmissionManager(self.mock_db_manager, self.mock_retrieval_manager)
        session.clear()

    def test_take_quiz_valid(self):
        quiz_id = 1
        quiz_data = {
            'title': 'Sample Quiz',
            'questions': [
                {'question': 'Question 1?', 'options': ['A', 'B', 'C', 'D'], 'correct_option': 'A'},
                {'question': 'Question 2?', 'options': ['A', 'B', 'C', 'D'], 'correct_option': 'B'},
            ]
        }
        self.mock_retrieval_manager.get_quiz_by_id.return_value = quiz_data
        response = self.manager.take_quiz(quiz_id, 0)
        self.assertIn(b'take-quiz.html', response.data)
        self.assertIn(b'Sample Quiz', response.data)

    def test_take_quiz_invalid_question_num(self):
        quiz_id = 1
        self.mock_retrieval_manager.get_quiz_by_id.return_value = {'questions': []}
        response = self.manager.take_quiz(quiz_id, 1)
        self.assertEqual(response.status_code, 302)
        self.assertIn('home', response.location)

    def test_submit_quiz_answer_correct(self):
        quiz_id = 1
        question_num = 0
        correct_answer = 'A'
        quiz_data = {
            'title': 'Sample Quiz',
            'questions': [
                {'question': 'Question 1?', 'options': ['A', 'B', 'C', 'D'], 'correct_option': correct_answer}
            ]
        }
        self.mock_retrieval_manager.get_quiz_by_id.return_value = quiz_data
        with patch('flask.request.form', {'answer': correct_answer}):
            session['current_score'] = 0
            response = self.manager.submit_quiz_answer(quiz_id, question_num)
        self.assertEqual(session['current_score'], 1)
        self.assertEqual(response.status_code, 302)

    def test_submit_quiz_answer_incorrect(self):
        quiz_id = 1
        question_num = 0
        incorrect_answer = 'B'
        quiz_data = {
            'title': 'Sample Quiz',
            'questions': [
                {'question': 'Question 1?', 'options': ['A', 'B', 'C', 'D'], 'correct_option': 'A'}
            ]
        }
        self.mock_retrieval_manager.get_quiz_by_id.return_value = quiz_data
        with patch('flask.request.form', {'answer': incorrect_answer}):
            session['current_score'] = 0
            response = self.manager.submit_quiz_answer(quiz_id, question_num)
        self.assertEqual(session.get('current_score'), 0)
        self.assertEqual(response.status_code, 302)

    def test_score_render(self):
        quiz_id = 1
        score = 5
        total = 10
        response = self.manager.score(quiz_id, score, total)
        self.assertIn(b'score.html', response.data)
        self.assertIn(b'Score: 5', response.data)
        self.assertIn(b'Total Questions: 10', response.data)

    def test_penalty_render(self):
        quiz_id = 1
        question_num = 0
        quiz_data = {
            'title': 'Sample Quiz',
            'questions': [
                {'question': 'Question 1?', 'options': ['A', 'B', 'C', 'D'], 'correct_option': 'A'}
            ]
        }
        self.mock_retrieval_manager.get_quiz_by_id.return_value = quiz_data
        response = self.manager.penalty(quiz_id, question_num)
        self.assertIn(b'penalty.html', response.data)
        self.assertIn(b'Sample Quiz', response.data)
        self.assertIn(b'Current Score:', response.data)

if __name__ == '__main__':
    unittest.main()
