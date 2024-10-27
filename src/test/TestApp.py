import unittest
from unittest.mock import patch, MagicMock
from flask import session
from src.server.App import App
class AppTestCase(unittest.TestCase):

    def setUp(self):
        """Set up the test client and mock managers for each test."""
        self.app_instance = App()
        self.app = self.app_instance.app
        self.client = self.app.test_client()
        self.app.config['TESTING'] = True
        self.app_instance.db_manager = MagicMock()
        self.app_instance.quiz_manager = MagicMock()
        self.app_instance.user_manager = MagicMock()

    def test_index_route(self):
        """Test the index route and its redirection logic."""
        with self.client as client:
            with client.session_transaction() as sess:
                sess['email'] = None
            response = client.get('/')
            self.assertEqual(response.status_code, 200)
            self.assertIn(b'index.html', response.data)  
            self.app_instance.user_manager.is_signed_in.return_value = True
            response = client.get('/')
            self.assertEqual(response.status_code, 302)
            self.assertIn('/home', response.location)

    def test_add_user_route(self):
        """Test the user registration endpoint."""
        with self.client as client:
            self.app_instance.user_manager.add_user.return_value = True
            response = client.post('/add_user', data={'email': 'test@example.com', 'password': 'testpass'})
            self.assertEqual(response.status_code, 302)
            self.app_instance.user_manager.add_user.assert_called_once()

    def test_login_route(self):
        """Test login functionality."""
        with self.client as client:
            response = client.get('/login')
            self.assertEqual(response.status_code, 200)
            self.app_instance.user_manager.login.return_value = True
            response = client.post('/login', data={'email': 'test@example.com', 'password': 'testpass'})
            self.assertEqual(response.status_code, 302)
            self.assertIn('/home', response.location)
            self.app_instance.user_manager.login.return_value = False
            response = client.post('/login', data={'email': 'test@example.com', 'password': 'wrongpass'})
            self.assertIn(b'Invalid credentials', response.data)

    def test_logout_route(self):
        """Test logout functionality."""
        with self.client as client:
            with client.session_transaction() as sess:
                sess['email'] = 'test@example.com'
            response = client.get('/logout')
            self.assertEqual(response.status_code, 302)
            self.assertIn('/index', response.location)

    def test_create_quiz(self):
        """Test quiz creation route."""
        with self.client as client:
            self.app_instance.quiz_manager.create_quiz.return_value = True
            response = client.post('/create-quiz', data={'title': 'Sample Quiz', 'questions': []})
            self.assertEqual(response.status_code, 302)  
            self.app_instance.quiz_manager.create_quiz.assert_called_once()

    def test_submit_quiz(self):
        """Test quiz submission route."""
        with self.client as client:
            self.app_instance.quiz_manager.submit_quiz.return_value = True
            response = client.post('/submit-quiz', data={'answers': ['A', 'B', 'C']})
            self.assertEqual(response.status_code, 302)
            self.app_instance.quiz_manager.submit_quiz.assert_called_once()

    def test_quiz_detail(self):
        """Test retrieval of quiz details."""
        with self.client as client:
            self.app_instance.quiz_manager.quiz_detail.return_value = {'title': 'Sample Quiz', 'questions': []}
            response = client.get('/quiz/1')
            self.assertEqual(response.status_code, 200)
            self.assertIn(b'Sample Quiz', response.data)

    def test_take_quiz(self):
        """Test functionality of taking a quiz with questions."""
        with self.client as client:
            self.app_instance.quiz_manager.take_quiz.return_value = {'question': 'Sample question?', 'options': ['A', 'B', 'C', 'D']}
            response = client.get('/take-quiz/1/1')
            self.assertEqual(response.status_code, 200)
            self.assertIn(b'Sample question?', response.data)

    def test_submit_quiz_answer(self):
        """Test answer submission and scoring logic."""
        with self.client as client:
            self.app_instance.quiz_manager.submit_quiz_answer.return_value = True
            response = client.post('/submit-quiz-answer/1/1', data={'answer': 'A'})
            self.assertEqual(response.status_code, 302)
            self.app_instance.quiz_manager.submit_quiz_answer.assert_called_once()

    def test_penalty(self):
        """Test penalty application on incorrect answers."""
        with self.client as client:
            self.app_instance.quiz_manager.penalty.return_value = True
            response = client.get('/penalty/1/1')
            self.assertEqual(response.status_code, 302)
            self.app_instance.quiz_manager.penalty.assert_called_once()

    def tearDown(self):
        """Clean up after each test."""
        pass

if __name__ == '__main__':
    unittest.main()
