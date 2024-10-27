import unittest
from unittest.mock import MagicMock, patch
from flask import Flask, session, request
from src.server.QuizCreationManager import QuizCreationManager  # Assuming class is in quiz_creation_manager.py
from src.server.DatabaseManager import DatabaseManager  # Assuming DatabaseManager is in database_manager.py

class TestQuizCreationManager(unittest.TestCase):
    def setUp(self):
        self.db_manager = MagicMock(spec=DatabaseManager)
        self.quiz_manager = QuizCreationManager(self.db_manager)
        self.app = Flask(__name__)
        self.app.secret_key = 'test_secret'  # Necessary for Flask session testing

    @patch('flask.request')
    @patch('flask.session')
    def test_create_quiz_get_request(self, mock_session, mock_request):
        mock_request.method = 'GET'
        with self.app.app_context():
            response = self.quiz_manager.create_quiz()
            self.assertEqual(response.status_code, 200)

    @patch('flask.request')
    @patch('flask.flash')
    @patch('flask.session', {'email': 'test_user@example.com'})
    def test_create_quiz_post_with_limit(self, mock_flash, mock_request):
        mock_request.method = 'POST'
        mock_request.form = {'num_questions': '5', 'title': 'Test Quiz'}
        self.db_manager.execute_query.return_value = [(3,)]  # Mock reaching quiz limit
        with self.app.app_context():
            response = self.quiz_manager.create_quiz()
            mock_flash.assert_called_with("You have reached the maximum number of quizzes allowed (3).", "error")

    @patch('flask.request')
    def test_limit_questions(self, mock_request):
        result = self.quiz_manager.limit_questions(12)
        self.assertEqual(result, 10)  # Should limit to 10

        result = self.quiz_manager.limit_questions(8)
        self.assertEqual(result, 8)  # Should return 8 as it's below the limit

    @patch('flask.request')
    def test_build_questions_from_form(self, mock_request):
        mock_request.form = {
            'question_text_0': 'Question 1',
            'answer_0_1': 'Option 1',
            'answer_0_2': 'Option 2',
            'answer_0_3': 'Option 3',
            'answer_0_4': 'Option 4',
            'correct_answer_0': 'Option 1'
        }
        questions = self.quiz_manager.build_questions_from_form()
        self.assertEqual(len(questions), 1)
        self.assertEqual(questions[0][0], 'Question 1')
        self.assertEqual(questions[0][5], 'Option 1')

    @patch('flask.session', {'email': 'test_user@example.com'})
    def test_has_reached_quiz_limit(self):
        self.db_manager.execute_query.return_value = [(3,)]  # Simulate limit reached
        result = self.quiz_manager.has_reached_quiz_limit('test_user@example.com')
        self.assertTrue(result)

        self.db_manager.execute_query.return_value = [(2,)]
        result = self.quiz_manager.has_reached_quiz_limit('test_user@example.com')
        self.assertFalse(result)

    @patch('flask.request')
    def test_get_quiz_details_from_form(self, mock_request):
        mock_request.form = {'num_questions': '5', 'title': 'Sample Quiz'}
        num_questions, title = self.quiz_manager.get_quiz_details_from_form()
        self.assertEqual(num_questions, '5')
        self.assertEqual(title, 'Sample Quiz')

    def test_build_insert_query(self):
        questions = [
            ('What is 2+2?', '1', '2', '3', '4', '4')
        ]
        user_email = 'test_user@example.com'
        title = 'Math Quiz'
        columns, values, placeholders = self.quiz_manager.build_insert_query(questions, user_email, title)
        self.assertIn('question1', columns)
        self.assertIn('correct_option1', columns)
        self.assertEqual(values[0], 'test_user@example.com')
        self.assertEqual(values[1], 'Math Quiz')

    @patch('flask.request')
    @patch('flask.redirect')
    @patch('flask.url_for')
    def test_submit_quiz(self, mock_url_for, mock_redirect, mock_request):
        mock_request.method = 'POST'
        mock_request.form = {
            'title': 'Test Quiz',
            'question_text_0': 'Question 1',
            'answer_0_1': 'Option A',
            'answer_0_2': 'Option B',
            'answer_0_3': 'Option C',
            'answer_0_4': 'Option D',
            'correct_answer_0': 'Option A'
        }
        with self.app.app_context():
            response = self.quiz_manager.submit_quiz()
            mock_redirect.assert_called_once_with(mock_url_for('home'))
            self.db_manager.execute_commit.assert_called_once()

    @patch('flask.request')
    def test_render_quiz_creation_form(self, mock_request):
        with self.app.app_context():
            response = self.quiz_manager.render_quiz_creation_form(3, 'Sample Quiz')
            self.assertIn('Sample Quiz', response)

if __name__ == '__main__':
    unittest.main()
